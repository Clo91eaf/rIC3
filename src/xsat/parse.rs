use aig::{Aig, AigEdge};
use logicrs::{Lit, Var};
use std::collections::{HashMap, HashSet, VecDeque};

use super::gate::{GateType, GateVar, GateVarMap};

/// Result of parsing an AIGER file into the X-SAT circuit representation.
pub struct Circuit {
    pub vars: GateVarMap<GateVar>,
    pub num_vars: usize,
    pub num_inputs: usize,
    pub num_ands: usize,
    pub num_xors: usize,
    pub num_outputs: usize,
    pub inputs: Vec<Var>,
    pub outputs: Vec<Lit>,
}

/// Parse an AIGER file into the X-SAT circuit representation.
///
/// Corresponds to X-SAT `CSat::parse_aig()` (parse.cpp:100-250)
///
/// The process has four stages:
///   1. Read AIGER file using the existing aig-rs library
///   2. Detect XOR gates from AND gate patterns (is_xor_output)
///   3. Iteratively delete gates with no fanout (dead code elimination)
///   4. Renumber variables: inputs first, then AND/XOR gates
pub fn parse_aig(path: &str) -> Circuit {
    let aig = Aig::from_file(path);
    parse_aig_from(&aig)
}

/// Parse from an in-memory Aig struct (useful for testing).
pub fn parse_aig_from(aig: &Aig) -> Circuit {
    // --- Stage 1: Build internal XAGate representation ---
    //
    // X-SAT creates `XAGate *gates = new XAGate[num_vars + 1]` (parse.cpp:128)
    // where num_vars = num_inputs + num_ands.
    // We use a HashMap keyed by AIG node id instead.

    let num_inputs = aig.inputs.len();
    let num_ands = aig.nodes.iter().filter(|n| n.is_and()).count();
    let raw_num_vars = num_inputs + num_ands;

    // XAGate equivalent: stores gate type and fanin for each AIG node
    // X-SAT parse.cpp:119-127
    struct XAGate {
        gate_type: GateType,
        fanin0: AigEdge,
        fanin1: AigEdge,
        fanouts: HashSet<usize>,
        is_output: bool,
        deleted: bool,
    }

    let mut gates: HashMap<usize, XAGate> = HashMap::new();

    // Initialize input gates
    // X-SAT parse.cpp:193-201 — inputs are added first with type INPUT
    for &input_id in &aig.inputs {
        gates.insert(
            input_id,
            XAGate {
                gate_type: GateType::Input,
                fanin0: AigEdge::constant(false),
                fanin1: AigEdge::constant(false),
                fanouts: HashSet::new(),
                is_output: false,
                deleted: false,
            },
        );
    }
    // Process AND gates — detect XOR and build fanout
    // X-SAT parse.cpp:131-147
    for node in aig.nodes.iter() {
        if node.is_and() {
            let lhs = node.node_id();
            let rhs0 = node.fanin0();
            let rhs1 = node.fanin1();

            // --- Stage 2: XOR recovery ---
            // X-SAT: is_xor_output() (parse.cpp:47-98)
            let (gate_type, fanin0, fanin1) = detect_xor_gate(aig, rhs0, rhs1, num_inputs);

            // Build fanout links
            // X-SAT parse.cpp:145-146
            let fanin0_var = fanin0.node_id();
            let fanin1_var = fanin1.node_id();
            if let Some(g) = gates.get_mut(&fanin0_var) {
                g.fanouts.insert(lhs);
            }
            if fanin1_var != fanin0_var {
                if let Some(g) = gates.get_mut(&fanin1_var) {
                    g.fanouts.insert(lhs);
                }
            }

            gates.insert(
                lhs,
                XAGate {
                    gate_type,
                    fanin0,
                    fanin1,
                    fanouts: HashSet::new(),
                    is_output: false,
                    deleted: false,
                },
            );
        }
    }

    // Mark output nodes
    // X-SAT parse.cpp:148-151
    for out_edge in &aig.outputs {
        let var = out_edge.node_id();
        if let Some(g) = gates.get_mut(&var) {
            g.is_output = true;
        }
    }

    // --- Stage 3: Dead gate elimination ---
    // X-SAT parse.cpp:153-176
    // Iteratively remove gates with no fanout that are not outputs.
    let mut queue: VecDeque<usize> = VecDeque::new();
    for (&var, gate) in &gates {
        if gate.fanouts.is_empty() && !gate.is_output && gate.gate_type != GateType::Input {
            queue.push_back(var);
        }
    }
    // Also check input gates with no fanout
    for (&var, gate) in &gates {
        if gate.fanouts.is_empty() && !gate.is_output && gate.gate_type == GateType::Input {
            queue.push_back(var);
        }
    }

    let mut deleted_set: HashSet<usize> = HashSet::new();
    while let Some(var) = queue.pop_front() {
        if deleted_set.contains(&var) {
            continue;
        }
        deleted_set.insert(var);
        if let Some(gate) = gates.get_mut(&var) {
            gate.deleted = true;

            // Remove this gate from its fanin gates' fanout sets
            // X-SAT parse.cpp:165-170
            if gate.gate_type != GateType::Input {
                let fi0 = gate.fanin0.node_id();
                let fi1 = gate.fanin1.node_id();
                if let Some(g) = gates.get_mut(&fi0) {
                    g.fanouts.remove(&var);
                    if g.fanouts.is_empty() && !g.is_output {
                        queue.push_back(fi0);
                    }
                }
                if fi1 != fi0 {
                    if let Some(g) = gates.get_mut(&fi1) {
                        g.fanouts.remove(&var);
                        if g.fanouts.is_empty() && !g.is_output {
                            queue.push_back(fi1);
                        }
                    }
                }
            }
        }
    }

    let num_deleted = deleted_set.len();

    // --- Stage 4: Renumber variables ---
    // X-SAT parse.cpp:186-243
    // Inputs get numbered first (1..num_inputs), then AND/XOR gates.

    let final_num_vars = raw_num_vars - num_deleted;
    let mut id_map: HashMap<usize, Var> = HashMap::new();
    let mut next_id: u32 = 0;

    let mut get_id = |aig_var: usize| -> Var {
        if let Some(&v) = id_map.get(&aig_var) {
            v
        } else {
            next_id += 1;
            let v = Var(next_id);
            id_map.insert(aig_var, v);
            v
        }
    };

    let mut vars = GateVarMap::<GateVar>::with_capacity(final_num_vars + 1);
    let mut inputs: Vec<Var> = Vec::new();
    let mut outputs: Vec<Lit> = Vec::new();
    let mut num_ands = 0;
    let mut num_xors = 0;

    // Number inputs first — X-SAT parse.cpp:193-201
    for &input_id in &aig.inputs {
        if deleted_set.contains(&input_id) {
            continue;
        }
        let var = get_id(input_id);
        vars.reserve(var);
        vars.set(var, GateVar::new(GateType::Input));
        inputs.push(var);
    }

    // Collect AND/XOR gate info: (aig_id, gate_type, fanin0_edge, fanin1_edge)
    // We need to assign all IDs first, then resolve literals.
    let mut gate_list: Vec<(Var, GateType, AigEdge, AigEdge)> = Vec::new();
    for node in aig.nodes.iter() {
        if !node.is_and() {
            continue;
        }
        let aig_id = node.node_id();
        if deleted_set.contains(&aig_id) {
            continue;
        }
        let gate = &gates[&aig_id];
        let var = get_id(aig_id);
        vars.reserve(var);
        gate_list.push((var, gate.gate_type, gate.fanin0, gate.fanin1));
    }

    // Now resolve literals (id_map is fully populated)
    for (var, gate_type, fi0_edge, fi1_edge) in gate_list {
        let fi0_lit = Lit::new(id_map[&fi0_edge.node_id()], !fi0_edge.compl());
        let fi1_lit = Lit::new(id_map[&fi1_edge.node_id()], !fi1_edge.compl());

        let mut gv = GateVar::new(gate_type);
        gv.fanin.push(fi0_lit);
        gv.fanin.push(fi1_lit);

        match gate_type {
            GateType::And => num_ands += 1,
            GateType::Xor => num_xors += 1,
            _ => unreachable!(),
        }

        vars.set(var, gv);
    }

    // Mark outputs — X-SAT parse.cpp:228-233
    let num_outputs = aig.outputs.len();
    for out_edge in &aig.outputs {
        let aig_var = out_edge.node_id();
        if deleted_set.contains(&aig_var) {
            continue;
        }
        let var = id_map[&aig_var];
        vars[var].is_output = true;
        outputs.push(Lit::new(var, !out_edge.compl()));
    }

    let num_inputs = inputs.len();

    Circuit {
        vars,
        num_vars: final_num_vars,
        num_inputs,
        num_ands,
        num_xors,
        num_outputs,
        inputs,
        outputs,
    }
}

/// Detect if an AND gate is actually an XOR gate encoded in AIG form.
///
/// Corresponds to X-SAT `is_xor_output()` (parse.cpp:47-98)
///
/// ## XOR encoding in AIGER
///
/// AIGER only supports AND gates. XOR(a, b) is encoded as:
///
/// The outer AND has both inputs negated, and each sub-AND has complementary
/// polarities on the same pair of variables.
///
/// ## How detection works
///
/// Given gate `out = AND(rhs0, rhs1)`:
/// 1. Both rhs0 and rhs1 must be negated (sign check)
/// 2. rhs0 and rhs1 must themselves be AND gates
/// 3. The two sub-ANDs must share the same pair of variables
/// 4. The polarity pattern must match XOR (not XNOR)
///
/// ## Polarity patterns
///
/// Let the four signs be: (sign of sub-AND0 input0, sub-AND0 input1, sub-AND1 input0, sub-AND1 input1)
///
/// XOR:  (1,1,0,0) or (0,0,1,1) — one sub-AND negates var0, the other negates var1
/// XNOR: (0,1,1,0) or (1,0,0,1) — both sub-ANDs negate the same variable
///
/// For XNOR, we flip one input to convert to XOR: lit1 gets negated.
fn detect_xor_gate(
    aig: &Aig,
    rhs0: AigEdge,
    rhs1: AigEdge,
    num_inputs: usize,
) -> (GateType, AigEdge, AigEdge) {
    // X-SAT parse.cpp:52-53 — both inputs must be AND gates (not inputs/constants)
    // INDEX(LIT) = aiger_lit2var(LIT) - num_inputs - 1
    // If < 0, it's an input or constant, not an AND gate
    let rhs0_id = rhs0.node_id();
    let rhs1_id = rhs1.node_id();

    // Both inputs must be negated (complemented)
    // X-SAT parse.cpp:54 — !aiger_sign(gate.rhs0) || !aiger_sign(gate.rhs1)
    // Note: aiger_sign returns 1 for complemented, so X-SAT checks if NOT complemented
    // But in X-SAT's encoding, rhs0/rhs1 from the outer AND being complemented means
    // the outer AND takes ~v1, ~v2 as inputs.
    if !rhs0.compl() || !rhs1.compl() {
        return (GateType::And, rhs0, rhs1);
    }

    // Both inputs must be AND gates
    let node0 = &aig.nodes[rhs0_id];
    let node1 = &aig.nodes[rhs1_id];
    if !node0.is_and() || !node1.is_and() {
        return (GateType::And, rhs0, rhs1);
    }

    // Check that node_id > num_inputs (it's an AND gate, not an input)
    if rhs0_id <= num_inputs || rhs1_id <= num_inputs {
        return (GateType::And, rhs0, rhs1);
    }

    let (g0r0, g0r1) = node0.fanin();
    let (g1r0, g1r1) = node1.fanin();

    // Normalize: sort each pair by node_id
    // X-SAT parse.cpp:61-62
    let (g0_lo, g0_hi) = if g0r0.node_id() <= g0r1.node_id() {
        (g0r0, g0r1)
    } else {
        (g0r1, g0r0)
    };
    let (g1_lo, g1_hi) = if g1r0.node_id() <= g1r1.node_id() {
        (g1r0, g1r1)
    } else {
        (g1r1, g1r0)
    };

    // X-SAT parse.cpp:65 — the two sub-ANDs must share the same variable pair
    if g0_lo.node_id() != g1_lo.node_id() || g0_hi.node_id() != g1_hi.node_id() {
        return (GateType::And, rhs0, rhs1);
    }

    let sign00 = g0_lo.compl();
    let sign01 = g0_hi.compl();
    let sign10 = g1_lo.compl();
    let sign11 = g1_hi.compl();

    // X-SAT parse.cpp:76 — XOR pattern: (1,1,0,0) or (0,0,1,1)
    if (sign00 && sign01 && !sign10 && !sign11) || (!sign00 && !sign01 && sign10 && sign11) {
        // X-SAT parse.cpp:78-79: lit0 = var0*2, lit1 = var1*2 (both positive)
        let lit0 = AigEdge::new(g0_lo.node_id(), false);
        let lit1 = AigEdge::new(g0_hi.node_id(), false);
        return (GateType::Xor, lit0, lit1);
    }

    // X-SAT parse.cpp:86 — XNOR pattern: (0,1,1,0) or (1,0,0,1)
    if (!sign00 && sign01 && sign10 && !sign11) || (sign00 && !sign01 && !sign10 && sign11) {
        // X-SAT parse.cpp:88-89: lit0 = var0*2, lit1 = var1*2+1 (flip one input)
        let lit0 = AigEdge::new(g0_lo.node_id(), false);
        let lit1 = AigEdge::new(g0_hi.node_id(), true);
        return (GateType::Xor, lit0, lit1);
    }

    // Not an XOR pattern — keep as AND
    (GateType::And, rhs0, rhs1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn data_dir() -> &'static str {
        "/home/clo91eaf/Project/X-SAT/data"
    }

    fn find_aiger(name: &str) -> Option<String> {
        let path = format!("{}/airthmetic/{}.aiger", data_dir(), name);
        if Path::new(&path).exists() {
            return Some(path);
        }
        let path = format!("{}/non-airthmetic/{}.aiger", data_dir(), name);
        if Path::new(&path).exists() {
            return Some(path);
        }
        None
    }

    #[test]
    fn test_parse_small_circuit() {
        // Use the smallest available benchmark
        let path = find_aiger("ac1").unwrap();
        let circuit = parse_aig(&path);

        // Basic sanity checks
        assert!(circuit.num_vars > 0);
        assert!(circuit.num_inputs > 0);
        assert!(circuit.num_outputs > 0);
        assert_eq!(
            circuit.num_vars,
            circuit.num_ands + circuit.num_xors + circuit.num_inputs
        );

        // Verify input variables have correct type
        for &v in &circuit.inputs {
            assert_eq!(circuit.vars[v].gate_type, GateType::Input);
            assert!(circuit.vars[v].is_input);
        }

        // Verify output variables are marked
        let mut output_vars: HashSet<Var> = HashSet::new();
        for lit in &circuit.outputs {
            output_vars.insert(lit.var());
        }
        for &v in &output_vars {
            assert!(circuit.vars[v].is_output);
        }
    }

    #[test]
    fn test_xor_recovery_arithmetic() {
        // Arithmetic circuits should have XOR gates
        let path = find_aiger("ac1").unwrap();
        let circuit = parse_aig(&path);
        println!(
            "ac1: vars={}, inputs={}, ands={}, xors={}",
            circuit.num_vars, circuit.num_inputs, circuit.num_ands, circuit.num_xors
        );
        // Arithmetic circuits use adders which contain XOR gates
        assert!(circuit.num_xors > 0);
    }

    #[test]
    fn test_all_benchmarks_parse() {
        // Verify all benchmarks parse without panic
        let entries = [(data_dir(), "airthmetic"), (data_dir(), "non-airthmetic")];
        for (base, subdir) in entries {
            let dir = format!("{}/{}", base, subdir);
            if let Ok(entries) = std::fs::read_dir(&dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.extension().map(|e| e == "aiger").unwrap_or(false) {
                        let name = path.file_stem().unwrap().to_str().unwrap();
                        let circuit = parse_aig(path.to_str().unwrap());
                        assert_eq!(
                            circuit.num_vars,
                            circuit.num_ands + circuit.num_xors + circuit.num_inputs,
                            "Invariant violated for {}: vars={} but ands+{}+xors+{}+inputs+{} = {}",
                            name,
                            circuit.num_vars,
                            circuit.num_ands,
                            circuit.num_xors,
                            circuit.num_inputs,
                            circuit.num_ands + circuit.num_xors + circuit.num_inputs
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_fanin_are_valid_vars() {
        let path = find_aiger("ac1").unwrap();
        let circuit = parse_aig(&path);

        // All fanin literals must reference valid, non-deleted variables
        for v in circuit
            .inputs
            .iter()
            .copied()
            .chain((1..=circuit.num_vars).map(|i| Var(i as u32)))
        {
            let gv = &circuit.vars[v];
            for &fanin_lit in &gv.fanin {
                let fanin_var = fanin_lit.var();
                assert!(
                    fanin_var <= Var(circuit.num_vars as u32),
                    "fanin var {} out of range (max {})",
                    fanin_var,
                    circuit.num_vars
                );
            }
        }
    }

    #[test]
    fn test_verify_against_cpp() {
        // These numbers come from running the C++ X-SAT with -e 0 (no elimination)
        // to get the pre-elimination parse stats.
        let cases = [
            // (filename, num_vars, num_inputs, num_ands, num_xors)
            // These numbers come from C++ X-SAT parse stage (after dead code elimination, before preprocessing)
            ("ac1", 16192, 120, 12624, 3448),
            ("ad1", 17340, 126, 13572, 3642),
        ];
        for (name, expected_vars, expected_inputs, expected_ands, expected_xors) in cases {
            let path = find_aiger(name).unwrap();
            let circuit = parse_aig(&path);
            assert_eq!(
                circuit.num_vars, expected_vars,
                "{}: num_vars mismatch",
                name
            );
            assert_eq!(
                circuit.num_inputs, expected_inputs,
                "{}: num_inputs mismatch",
                name
            );
            assert_eq!(
                circuit.num_ands, expected_ands,
                "{}: num_ands mismatch",
                name
            );
            assert_eq!(
                circuit.num_xors, expected_xors,
                "{}: num_xors mismatch",
                name
            );
        }
    }

    #[test]
    fn test_no_duplicate_inputs() {
        let path = find_aiger("ac1").unwrap();
        let circuit = parse_aig(&path);

        let mut seen = HashSet::new();
        for &v in &circuit.inputs {
            assert!(seen.insert(v), "duplicate input var {}", v);
        }
    }
}

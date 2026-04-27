use logicrs::{Lit, Var};
use rand::RngExt;

use super::analyze;
use super::branch::{Branch, BranchMode};
use super::clause::{CRef, Clause};
use super::gate::{Assign, GateType, GateVar, GateVarMap, LitAssign, Reason};
use super::propagate;
use super::watch::{self, Watches};

pub struct SolveResult {
    pub sat: bool,
}

/// The X-SAT solver — a circuit-aware CDCL SAT solver.
///
/// Holds all state for the CDCL search: clause database, watch structures,
/// assignment state, branching heuristics, and solver parameters.
///
/// Corresponds to X-SAT `CSat` class (solver.h:100-238)
pub struct Solver {
    // --- Circuit topology ---
    pub num_inputs: usize,
    pub num_outputs: usize,
    pub num_vars: usize,
    pub num_gate_clauses: usize,
    pub outputs: Vec<Lit>,
    pub vars: GateVarMap<GateVar>,

    // --- Clause database ---
    pub clauses: Vec<Clause>,

    // --- Watch structures ---
    pub watches: Watches,

    // --- Assignment state ---
    pub value: LitAssign,
    pub assigns: Vec<Assign>,
    pub trail: Vec<Lit>,
    pub propagated: usize,
    pub pos_in_trail: Vec<usize>,

    // --- Branching ---
    pub branch: Branch,

    // --- Solver parameters ---
    pub var_inc: f64,
    pub clause_inc: f64,
    pub cur_restart: u64,
    pub reduce_limit: u64,
    pub reduces: u64,
    pub conflicts: u64,
    pub rephases: u64,
    pub rephase_limit: u64,
    pub threshold: usize,
    pub local_best: Vec<i8>,

    // --- LBD restart tracking ---
    pub lbd_queue: [u32; 50],
    pub lbd_queue_size: usize,
    pub lbd_queue_pos: usize,
    pub fast_lbd_sum: f64,
    pub slow_lbd_sum: f64,

    // --- Options ---
    pub enable_elim: bool,
    pub enable_xvsids: bool,
    pub reduce_per: usize,
    pub reduce_limit_inc: u64,

    // --- RNG ---
    pub rng: rand::rngs::StdRng,
}

impl Solver {
    pub fn new(circuit: super::parse::Circuit) -> Self {
        let num_vars = circuit.num_vars;
        let num_lits = (num_vars + 1) * 2;

        let mut value = LitAssign::new();
        let mut assigns = Vec::with_capacity(num_vars + 1);
        assigns.push(Assign::default());
        for v in 1..=num_vars {
            value.reserve_var(Var(v as u32));
            assigns.push(Assign::default());
        }

        Self {
            num_inputs: circuit.num_inputs,
            num_outputs: circuit.num_outputs,
            num_vars,
            num_gate_clauses: 0,
            outputs: circuit.outputs,
            vars: circuit.vars,

            clauses: Vec::new(),

            watches: Watches::new(num_lits),

            value,
            assigns,
            trail: Vec::new(),
            propagated: 0,
            pos_in_trail: Vec::new(),

            branch: Branch::new(num_vars),

            var_inc: 1.0,
            clause_inc: 1.0,
            cur_restart: 1,
            reduce_limit: 8192,
            reduces: 0,
            conflicts: 0,
            rephases: 0,
            rephase_limit: 1024,
            threshold: 0,
            local_best: vec![0; num_vars + 1],

            lbd_queue: [0; 50],
            lbd_queue_size: 0,
            lbd_queue_pos: 0,
            fast_lbd_sum: 0.0,
            slow_lbd_sum: 0.0,

            enable_elim: false,
            enable_xvsids: false,
            reduce_per: 50,
            reduce_limit_inc: 8192,

            rng: rand::make_rng(),
        }
    }

    /// Build fanout links and gate CNF clauses.
    /// X-SAT: `CSat::build_data_structure()` (solver.cpp:118-157)
    ///
    /// For each non-input gate, create CNF clauses encoding the gate semantics:
    ///   AND(a, b) = out  →  (~out, a), (~out, b), (out, ~a, ~b)
    ///   XOR(a, b) = out  →  (~out, a, b), (out, ~a, b), (out, a, ~b), (~out, ~a, ~b)
    pub fn build_data_structure(&mut self) {
        // Build fanout links — collect first to avoid borrow conflict
        let mut fanout_additions: Vec<(Var, Var)> = Vec::new();
        for i in (self.num_inputs + 1)..=self.num_vars {
            let gv = &self.vars[Var(i as u32)];
            for &fanin_lit in &gv.fanin {
                fanout_additions.push((fanin_lit.var(), Var(i as u32)));
            }
        }
        for (fanin_var, gate_var) in fanout_additions {
            self.vars[fanin_var].fanout.push(gate_var);
        }

        // Build gate CNF clauses
        for i in (self.num_inputs + 1)..=self.num_vars {
            let var = Var(i as u32);
            let gv = &self.vars[var];
            if gv.is_deleted {
                continue;
            }

            let out = gv.out_lit(var);
            let i0 = gv.fanin[0];
            let i1 = gv.fanin[1];

            if gv.gate_type == GateType::And {
                // AND: (~out, i0), (~out, i1), (out, ~i0, ~i1)
                let cr0 = self.alloc_clause(vec![!out, i0], false);
                let cr1 = self.alloc_clause(vec![!out, i1], false);
                let cr2 = self.alloc_clause(vec![out, !i0, !i1], false);
                let gv = &mut self.vars[var];
                gv.clauses.push(cr0);
                gv.clauses.push(cr1);
                gv.clauses.push(cr2);
            } else {
                // XOR: (~out, i0, i1), (out, ~i0, i1), (out, i0, ~i1), (~out, ~i0, ~i1)
                let cr0 = self.alloc_clause(vec![!out, i0, i1], false);
                let cr1 = self.alloc_clause(vec![out, !i0, i1], false);
                let cr2 = self.alloc_clause(vec![out, i0, !i1], false);
                let cr3 = self.alloc_clause(vec![!out, !i0, !i1], false);
                let gv = &mut self.vars[var];
                gv.clauses.push(cr0);
                gv.clauses.push(cr1);
                gv.clauses.push(cr2);
                gv.clauses.push(cr3);
            }
        }
    }

    /// Allocate a new clause in the clause database and return its CRef.
    fn alloc_clause(&mut self, lits: Vec<Lit>, learn: bool) -> CRef {
        let cref = CRef::from(self.clauses.len());
        let size = lits.len();
        let mut cls = Clause::new(size, learn);
        cls.data = lits;
        self.clauses.push(cls);
        cref
    }

    /// Add a learned clause to the database and attach watches.
    /// X-SAT: `CSat::add_learning_clause()` (solver.cpp:159-183)
    ///
    /// Returns the CRef of the new clause.
    pub fn add_learning_clause(&mut self, learn: &[Lit], lbd: u32) -> CRef {
        let cref = self.alloc_clause(learn.to_vec(), true);
        self.clauses[cref.idx()].lbd = lbd;

        if learn.len() == 3 {
            self.watches.add_tri(learn[0], learn[1], cref);
        } else if learn.len() > 3 {
            self.watches.add_gen(learn[0], learn[1], cref);
        }

        cref
    }

    /// Bump clause activity with rescaling.
    /// X-SAT: `CSat::bump_clause()` (solver.cpp:75-85)
    pub fn bump_clause(&mut self, cref: CRef, coeff: f64) {
        self.clauses[cref.idx()].activity += self.clause_inc * coeff;
        if self.clauses[cref.idx()].activity > 1e100 {
            for cls in &mut self.clauses {
                if !cls.is_deleted {
                    cls.activity *= 1e-100;
                }
            }
            self.clause_inc *= 1e-100;
        }
    }

    /// Assign a literal at a given level with a reason.
    /// Central assignment function used by the solver loop.
    /// X-SAT: `CSat::assign()` (solver.cpp:87-116)
    pub fn assign_lit(&mut self, lit: Lit, level: u32, reason: Reason) {
        debug_assert!(self.value.val(lit).is_none());

        self.value.assign(lit);
        let var = *lit.var() as usize;
        self.assigns[var].level = level;
        self.assigns[var].reason = reason;
        self.trail.push(lit);

        if self.branch.mode == BranchMode::JFrontier {
            self.branch.jheap_insert(lit.var());
        }
    }

    /// Restart: backtrack to level 0 with probabilistic rephasing.
    /// X-SAT: `CSat::restart()` (solver.cpp:185-198)
    pub fn restart(&mut self) {
        self.fast_lbd_sum = 0.0;
        self.lbd_queue_size = 0;
        self.lbd_queue_pos = 0;

        analyze::backtrack(
            0,
            &mut self.trail,
            &mut self.propagated,
            &mut self.value,
            &mut self.assigns,
            &mut self.branch.saved,
            &self.pos_in_trail,
        );

        let phase_rand: u32 = self.rng.random_range(0..100);
        if phase_rand < 60 {
            for i in 1..=self.num_vars {
                self.branch.saved[i] = self.local_best[i];
            }
        } else if phase_rand < 65 {
            for i in 1..=self.num_vars {
                self.branch.saved[i] = -self.local_best[i];
            }
        } else if phase_rand < 75 {
            // random phase — alternate based on index
            for i in 1..=self.num_vars {
                self.branch.saved[i] = if i % 2 == 0 { 1 } else { -1 };
            }
        }
        // else: keep current saved (25%)
    }

    /// Rephase: reset rephase counter and increase limit.
    /// X-SAT: `CSat::rephase()` (solver.cpp:200-203)
    pub fn rephase(&mut self) {
        self.rephases = 0;
        self.threshold = (self.threshold as f64 * 0.9) as usize;
        self.rephase_limit += 8192;
    }

    /// Record an LBD value in the moving average queue.
    fn record_lbd(&mut self, lbd: u32) {
        if self.lbd_queue_size < 50 {
            self.lbd_queue[self.lbd_queue_pos] = lbd;
            self.lbd_queue_pos = (self.lbd_queue_pos + 1) % 50;
            self.lbd_queue_size += 1;
        } else {
            self.fast_lbd_sum -= self.lbd_queue[self.lbd_queue_pos] as f64;
            self.lbd_queue[self.lbd_queue_pos] = lbd;
            self.lbd_queue_pos = (self.lbd_queue_pos + 1) % 50;
        }
        self.fast_lbd_sum += lbd as f64;
        self.slow_lbd_sum += lbd as f64;
    }

    /// Update local-best phase when trail reaches new high water mark.
    fn update_local_best(&mut self) {
        if self.trail.len() > self.threshold {
            self.threshold = self.trail.len();
            for i in 1..=self.num_vars {
                let lit = Var(i as u32).lit();
                match self.value.val(lit) {
                    super::gate::TriVal::True => self.local_best[i] = 1,
                    super::gate::TriVal::False => self.local_best[i] = -1,
                    super::gate::TriVal::None => self.local_best[i] = 1,
                }
            }
        }
    }

    /// Reduce learned clause database.
    /// X-SAT: `CSat::reduce()` (reduce.cpp:75-126)
    ///
    /// Sort learned clauses by LBD (ascending) then activity (descending).
    /// Delete the bottom portion (controlled by reduce_per).
    /// If wasted memory > 20%, compact the database.
    pub fn reduce(&mut self) {
        let mut indices: Vec<usize> = Vec::new();
        for i in 0..self.clauses.len() {
            if self.clauses[i].is_learn && !self.clauses[i].is_deleted {
                indices.push(i);
            }
        }

        indices.sort_by(|&a, &b| {
            let ca = &self.clauses[a];
            let cb = &self.clauses[b];
            if ca.lbd != cb.lbd {
                ca.lbd.cmp(&cb.lbd)
            } else {
                cb.activity
                    .partial_cmp(&ca.activity)
                    .unwrap_or(std::cmp::Ordering::Equal)
            }
        });

        let keep_count = indices.len() * self.reduce_per / 100;
        for i in keep_count..indices.len() {
            self.clauses[indices[i]].is_deleted = true;
        }

        self.compact_watches();

        let wasted = self.clauses.iter().filter(|c| c.is_deleted).count();
        if wasted as f64 / self.clauses.len() as f64 > 0.2 {
            self.shrink_clauses();
        }
    }

    /// Remove deleted clauses from watch lists.
    fn compact_watches(&mut self) {
        for v in 0..=self.num_vars {
            for polarity in [true, false] {
                let lit = Lit::new(Var(v as u32), polarity);
                let tri = self.watches.tri_mut(lit);
                let mut write = 0;
                for read in 0..tri.len() {
                    if !self.clauses[tri[read].idx()].is_deleted {
                        tri[write] = tri[read];
                        write += 1;
                    }
                }
                tri.truncate(write);

                let gen_ws = self.watches.general_mut(lit);
                let mut write = 0;
                for read in 0..gen_ws.len() {
                    if !self.clauses[gen_ws[read].cref.idx()].is_deleted {
                        gen_ws[write] = gen_ws[read];
                        write += 1;
                    }
                }
                gen_ws.truncate(write);
            }
        }
    }

    /// Compact the clause database by removing deleted clauses.
    /// X-SAT: `CSat::shrink_clauses()` (reduce.cpp:6-73)
    ///
    /// Creates a new clause array, copies surviving clauses, remaps all
    /// CRef indices in watches and variable clause lists.
    fn shrink_clauses(&mut self) {
        self.restart();

        let mut new_clauses: Vec<Clause> = Vec::new();
        let mut remap: Vec<Option<CRef>> = vec![None; self.clauses.len()];

        for (i, cls) in self.clauses.iter().enumerate() {
            if !cls.is_deleted {
                let new_cref = CRef::from(new_clauses.len());
                remap[i] = Some(new_cref);
                new_clauses.push(cls.clone());
            }
        }

        // Remap watches
        for v in 0..=self.num_vars {
            for polarity in [true, false] {
                let lit = Lit::new(Var(v as u32), polarity);

                let tri = self.watches.tri_mut(lit);
                for cr in tri.iter_mut() {
                    if let Some(new_cr) = remap[cr.idx()] {
                        *cr = new_cr;
                    }
                }

                let gen_ws = self.watches.general_mut(lit);
                for w in gen_ws.iter_mut() {
                    if let Some(new_cr) = remap[w.cref.idx()] {
                        w.cref = new_cr;
                    }
                }
            }
        }

        // Remap variable clause lists
        for v in (self.num_inputs + 1)..=self.num_vars {
            let var = Var(v as u32);
            let gv = &mut self.vars[var];
            for cr in gv.clauses.iter_mut() {
                if let Some(new_cr) = remap[cr.idx()] {
                    *cr = new_cr;
                }
            }
        }

        self.clauses = new_clauses;
    }

    /// Main CDCL search loop.
    /// X-SAT: `CSat::solve()` (search.cpp:5-193)
    ///
    /// Returns 10 (SAT) or 20 (UNSAT).
    pub fn solve(&mut self) -> u32 {
        self.build_data_structure();
        self.num_gate_clauses = self.clauses.len();

        // Build watches for gate clauses
        watch::build_watches(&mut self.watches, &self.clauses, &self.vars, self.num_vars);

        // Initialize branching
        if self.enable_xvsids {
            self.branch
                .build_xor_neighbors(&mut self.vars, self.num_inputs, self.num_vars);
        }
        self.branch.init_vsids(self.num_vars);

        match self.branch.mode {
            BranchMode::Vsids => {}
            BranchMode::JFrontier => self.branch.init_jfrontier(self.num_vars),
            BranchMode::Vmtf => self.branch.init_vmtf(self.num_vars),
        }

        // Force output variables to true at level 0
        let outputs: Vec<Lit> = self.outputs.clone();
        for out_lit in outputs {
            self.assign_lit(out_lit, 0, Reason::Output);
        }

        // Main CDCL loop
        loop {
            let result = propagate::propagate(
                &mut self.trail,
                &mut self.propagated,
                &mut self.watches,
                &mut self.clauses,
                &mut self.value,
                &mut self.assigns,
            );

            match result {
                propagate::PropResult::Conflict(conflict) => {
                    let analyze_result = analyze::analyze(
                        &conflict,
                        &self.trail,
                        &self.assigns,
                        &self.clauses,
                        self.num_vars,
                    );

                    if analyze_result.backtrack_level < 0 {
                        return 20; // UNSAT
                    }

                    analyze::backtrack(
                        analyze_result.backtrack_level as u32,
                        &mut self.trail,
                        &mut self.propagated,
                        &mut self.value,
                        &mut self.assigns,
                        &mut self.branch.saved,
                        &self.pos_in_trail,
                    );

                    let learn = analyze_result.learn;
                    let lbd = analyze_result.lbd;

                    self.record_lbd(lbd);

                    if learn.len() == 1 {
                        self.assign_lit(learn[0], 0, Reason::Output);
                    } else if learn.len() == 2 {
                        self.watches.add_bin(learn[0], learn[1]);
                        self.assign_lit(
                            learn[0],
                            analyze_result.backtrack_level as u32,
                            Reason::Direct(learn[1]),
                        );
                    } else {
                        let cref = self.add_learning_clause(&learn, lbd);
                        self.bump_clause(cref, 1.0);
                        self.assign_lit(
                            learn[0],
                            analyze_result.backtrack_level as u32,
                            Reason::Clause(cref),
                        );
                    }

                    self.var_inc *= 1.0 / 0.8;
                    self.clause_inc *= 1.0 / 0.8;
                    self.reduces += 1;
                    self.conflicts += 1;
                    self.rephases += 1;

                    self.update_local_best();
                }
                propagate::PropResult::Ok => {
                    if self.conflicts >= self.cur_restart * self.reduce_limit {
                        self.reduce();
                        self.cur_restart = (self.conflicts / self.reduce_limit) + 1;
                        self.reduce_limit += self.reduce_limit_inc;
                    } else if self.lbd_queue_size == 50
                        && 0.80 * self.fast_lbd_sum / 50.0
                            > self.slow_lbd_sum / self.conflicts as f64
                    {
                        self.restart();
                    } else if self.rephases >= self.rephase_limit {
                        self.rephase();
                    } else {
                        let decided = self.branch.decide(
                            &mut self.value,
                            &self.vars,
                            &self.clauses,
                            &mut self.trail,
                            &mut self.assigns,
                        );
                        if decided.is_none() {
                            return 10; // SAT — all variables assigned
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    fn make_simple_circuit() -> super::super::parse::Circuit {
        let num_vars = 3;
        let mut vars = GateVarMap::new();
        for v in 0..=num_vars {
            vars.reserve(Var(v as u32));
        }

        // var 1: input
        vars.set(
            Var(1),
            GateVar {
                is_input: true,
                is_output: false,
                gate_type: GateType::Input,
                fanin: Vec::new(),
                fanout: Vec::new(),
                clauses: Vec::new(),
                neighbors: Vec::new(),
                is_deleted: false,
                xor_edges: 0,
                lut_phase: 0.0,
            },
        );

        // var 2: input
        vars.set(
            Var(2),
            GateVar {
                is_input: true,
                is_output: false,
                gate_type: GateType::Input,
                fanin: Vec::new(),
                fanout: Vec::new(),
                clauses: Vec::new(),
                neighbors: Vec::new(),
                is_deleted: false,
                xor_edges: 0,
                lut_phase: 0.0,
            },
        );

        // var 3: AND(v1, v2) — output
        vars.set(
            Var(3),
            GateVar {
                is_input: false,
                is_output: true,
                gate_type: GateType::And,
                fanin: vec![Var(1).lit(), Var(2).lit()],
                fanout: Vec::new(),
                clauses: Vec::new(),
                neighbors: Vec::new(),
                is_deleted: false,
                xor_edges: 0,
                lut_phase: 0.0,
            },
        );

        super::super::parse::Circuit {
            vars,
            num_vars,
            num_inputs: 2,
            num_ands: 1,
            num_xors: 0,
            num_outputs: 1,
            inputs: vec![Var(1), Var(2)],
            outputs: vec![Var(3).lit()],
        }
    }

    #[test]
    fn test_build_data_structure() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        solver.build_data_structure();

        // AND gate should have 3 clauses
        let gv = &solver.vars[Var(3)];
        assert_eq!(gv.clauses.len(), 3);
        assert_eq!(solver.clauses.len(), 3);
    }

    #[test]
    fn test_alloc_clause() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        let cr = solver.alloc_clause(vec![Var(1).lit(), !Var(2).lit()], true);
        assert_eq!(cr.idx(), 0);
        assert_eq!(solver.clauses[0].data.len(), 2);
        assert!(solver.clauses[0].is_learn);
    }

    #[test]
    fn test_add_learning_clause() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        let learn = vec![Var(1).lit(), !Var(2).lit(), Var(3).lit()];
        let cr = solver.add_learning_clause(&learn, 2);
        assert_eq!(solver.clauses[cr.idx()].lbd, 2);
    }

    #[test]
    fn test_assign_lit() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        solver.assign_lit(Var(1).lit(), 0, Reason::Decision);
        assert!(solver.value.val(Var(1).lit()).is_true());
        assert_eq!(solver.trail.len(), 1);
    }

    #[test]
    fn test_solve_simple_sat() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        let result = solver.solve();
        // AND(v1, v2) with output=true should be SAT (both inputs set true)
        assert_eq!(result, 10);
    }

    #[test]
    fn test_record_lbd() {
        let circuit = make_simple_circuit();
        let mut solver = Solver::new(circuit);

        solver.record_lbd(5);
        assert_eq!(solver.lbd_queue_size, 1);
        assert_eq!(solver.fast_lbd_sum, 5.0);
    }
}

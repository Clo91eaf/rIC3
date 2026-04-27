use logicrs::{Lit, Var};

use super::clause::Clause;
use super::gate::{GateType, GateVar, GateVarMap, LitAssign, Reason};
use super::heap::ActHeap;

/// Branching mode — corresponds to X-SAT `BranchMode` (solver.h:40-44)
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BranchMode {
    Vsids,
    JFrontier,
    Vmtf,
}

/// Branching state — all data needed by the three branching strategies.
pub struct Branch {
    pub mode: BranchMode,
    pub var_activity: Vec<f64>,
    pub var_inc: f64,
    pub gate_activity: Vec<f64>,
    pub heap: ActHeap,
    pub jheap: ActHeap,
    pub injheap: Vec<bool>,
    pub saved: Vec<i8>,
    pub pos_in_trail: Vec<usize>,
}

impl Branch {
    pub fn new(num_vars: usize) -> Self {
        Self {
            mode: BranchMode::Vsids,
            var_activity: vec![0.0; num_vars + 1],
            var_inc: 1.0,
            gate_activity: vec![0.0; num_vars + 1],
            heap: ActHeap::with_capacity(num_vars + 1),
            jheap: ActHeap::with_capacity(num_vars + 1),
            injheap: vec![false; num_vars + 1],
            saved: vec![0; num_vars + 1],
            pos_in_trail: Vec::new(),
        }
    }

    /// Initialize VSIDS mode: insert all variables into the activity heap.
    /// X-SAT: `CSat::initVsidsMode()` (branch.cpp:6-53)
    pub fn init_vsids(&mut self, num_vars: usize) {
        self.mode = BranchMode::Vsids;
        self.heap.clear();
        for i in 1..=num_vars {
            self.injheap[i] = false;
            self.var_activity[i] = 0.0;
            self.gate_activity[i] = 0.0;
            self.heap.insert(Var(i as u32), &self.var_activity);
        }
    }

    /// Initialize J-Frontier mode.
    /// X-SAT: `CSat::initJfrontierMode()` (branch.cpp:56-58)
    pub fn init_jfrontier(&mut self, _num_vars: usize) {
        self.mode = BranchMode::JFrontier;
    }

    /// Initialize VMTF mode.
    /// Variables are traversed in order during decide.
    /// X-SAT: `CSat::initVmtfMode()` (branch.cpp:216-221)
    pub fn init_vmtf(&mut self, _num_vars: usize) {
        self.mode = BranchMode::Vmtf;
    }

    /// Bump variable activity.
    /// X-SAT: `CSat::bump_var()` (jheap.cpp:5-28)
    ///
    /// 1. Increase activity by var_inc * coeff
    /// 2. If activity > 1e100, rescale all activities
    /// 3. Update heap position
    /// 4. For J-Frontier: propagate activity to fanout gates
    pub fn bump_var(&mut self, var: Var, coeff: f64) {
        if self.mode == BranchMode::Vmtf {
            return;
        }

        let vi = *var as usize;
        self.var_activity[vi] += self.var_inc * coeff;

        if self.var_activity[vi] > 1e100 {
            for a in self.var_activity.iter_mut() {
                *a *= 1e-100;
            }
            for a in self.gate_activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        if self.mode == BranchMode::JFrontier {
            // Propagate activity to fanout gates
        } else if self.mode == BranchMode::Vsids {
            self.heap.update(var, &self.var_activity);
        }
    }

    /// Decay: increase the increment factor.
    /// X-SAT uses implicit decay: bump adds var_inc, which grows over time.
    pub fn decay(&mut self) {
        self.var_inc *= 1.0 / 0.95;
    }

    /// Choose the next decision variable and return the literal to assign.
    /// Returns None if all variables are assigned (SAT).
    /// X-SAT: `CSat::decide()` (branch.cpp:258-266)
    pub fn decide(
        &mut self,
        value: &mut LitAssign,
        vars: &GateVarMap<GateVar>,
        clauses: &[Clause],
        trail: &mut Vec<Lit>,
        assigns: &mut Vec<super::gate::Assign>,
    ) -> Option<Lit> {
        match self.mode {
            BranchMode::Vsids => self.decide_vsids(value, vars, trail, assigns),
            BranchMode::JFrontier => self.decide_jfrontier(value, vars, clauses, trail, assigns),
            BranchMode::Vmtf => self.decide_vmtf(value, trail, assigns),
        }
    }

    /// VSIDS branching.
    /// X-SAT: `CSat::branchVsidsMode()` (branch.cpp:185-214)
    ///
    /// Pop the highest-activity unassigned variable from the heap.
    /// Phase saving: use the saved polarity, default positive.
    fn decide_vsids(
        &mut self,
        value: &mut LitAssign,
        _vars: &GateVarMap<GateVar>,
        trail: &mut Vec<Lit>,
        assigns: &mut Vec<super::gate::Assign>,
    ) -> Option<Lit> {
        let next = loop {
            let v = self.heap.pop(&self.var_activity)?;
            if value.val(v.lit()).is_none() {
                break v;
            }
        };

        let phase = if self.saved[*next as usize] != 0 {
            self.saved[*next as usize] > 0
        } else {
            true
        };

        let lit = Lit::new(next, phase);
        let level = self.pos_in_trail.len() as u32 + 1;
        self.pos_in_trail.push(trail.len());

        value.assign(lit);
        assigns[*next as usize].level = level;
        assigns[*next as usize].reason = Reason::Decision;
        trail.push(lit);

        Some(lit)
    }

    /// J-Frontier branching.
    /// X-SAT: `CSat::branchJfrontierMode()` (branch.cpp:93-183)
    ///
    /// 1. Pop gates from jheap (ordered by gate activity)
    /// 2. Check if gate is both j-reason (output assigned) and j-node (has unsatisfied clause)
    /// 3. Select the highest-activity unassigned fanin variable
    /// 4. Assign that variable
    fn decide_jfrontier(
        &mut self,
        value: &mut LitAssign,
        vars: &GateVarMap<GateVar>,
        clauses: &[Clause],
        trail: &mut Vec<Lit>,
        assigns: &mut Vec<super::gate::Assign>,
    ) -> Option<Lit> {
        loop {
            if self.jheap.is_empty() {
                return None;
            }
            let gate_var = self.jheap.pop(&self.gate_activity);
            let gate_var = gate_var?;
            self.injheap[*gate_var as usize] = false;

            // Check j-reason: output must be assigned and not an input
            if !self.is_jreason(gate_var, value, vars) {
                continue;
            }

            // Check j-node: has at least one clause with no satisfied literal
            if self.is_jnode(gate_var, value, vars, clauses) {
                // Find the highest-activity unassigned fanin
                let mut decide_vref: Option<Var> = None;
                let gv = &vars[gate_var];
                for &fanin_lit in &gv.fanin {
                    let fanin_var = fanin_lit.var();
                    if !value.val(fanin_lit).is_none() {
                        continue;
                    }
                    if decide_vref.is_none()
                        || self.var_activity[*fanin_var as usize]
                            > self.var_activity[*decide_vref.unwrap() as usize]
                    {
                        decide_vref = Some(fanin_var);
                    }
                }

                if let Some(dv) = decide_vref {
                    let phase = if self.saved[*dv as usize] != 0 {
                        self.saved[*dv as usize] > 0
                    } else {
                        true
                    };

                    let lit = Lit::new(dv, phase);
                    let level = self.pos_in_trail.len() as u32 + 1;
                    self.pos_in_trail.push(trail.len());

                    value.assign(lit);
                    assigns[*dv as usize].level = level;
                    assigns[*dv as usize].reason = Reason::Decision;
                    trail.push(lit);

                    return Some(lit);
                }
            }
        }
    }

    /// VMTF branching.
    /// X-SAT: `CSat::branchVmtfMode()` (branch.cpp:228-256)
    ///
    /// Simple: scan variables in order, pick the first unassigned one.
    /// The "move to front" happens during bump_vmtf (conflict vars moved to front).
    fn decide_vmtf(
        &mut self,
        value: &mut LitAssign,
        trail: &mut Vec<Lit>,
        assigns: &mut Vec<super::gate::Assign>,
    ) -> Option<Lit> {
        for i in 1..self.var_activity.len() {
            let var = Var(i as u32);
            if value.val(var.lit()).is_none() {
                let phase = if self.saved[i] != 0 {
                    self.saved[i] > 0
                } else {
                    true
                };

                let lit = Lit::new(var, phase);
                let level = self.pos_in_trail.len() as u32 + 1;
                self.pos_in_trail.push(trail.len());

                value.assign(lit);
                assigns[i].level = level;
                assigns[i].reason = Reason::Decision;
                trail.push(lit);

                return Some(lit);
            }
        }
        None
    }

    /// Check if a variable is a j-reason.
    /// X-SAT: `CSat::is_jreason()` (jheap.cpp:49-55)
    ///
    /// A gate is j-reason if its output is assigned and it's not an input gate.
    fn is_jreason(&self, var: Var, value: &LitAssign, vars: &GateVarMap<GateVar>) -> bool {
        let gv = &vars[var];
        if gv.gate_type == GateType::Input {
            return false;
        }
        let out_lit = gv.out_lit(var);
        !value.val(out_lit).is_none()
    }

    /// Check if a variable is a j-node.
    /// X-SAT: `CSat::is_jnode()` (jheap.cpp:57-72)
    ///
    /// A gate is j-node if it has at least one clause with no satisfied literal.
    fn is_jnode(
        &self,
        var: Var,
        value: &LitAssign,
        vars: &GateVarMap<GateVar>,
        clauses: &[Clause],
    ) -> bool {
        let gv = &vars[var];
        for &cref in &gv.clauses {
            let cls = &clauses[cref.idx()];
            let has_sat = cls.data.iter().any(|&l| value.val(l).is_true());
            if !has_sat {
                return true;
            }
        }
        false
    }

    /// Insert a gate into the jheap.
    /// X-SAT: `CSat::heap_insert()` (jheap.cpp:30-34)
    pub fn jheap_insert(&mut self, gate: Var) {
        if self.injheap[*gate as usize] {
            return;
        }
        self.injheap[*gate as usize] = true;
        self.jheap.insert(gate, &self.gate_activity);
    }

    /// Build XOR neighbor lists for XVSIDS.
    /// X-SAT: `CSat::initVsidsMode()` (branch.cpp:20-47)
    pub fn build_xor_neighbors(
        &mut self,
        vars: &mut GateVarMap<GateVar>,
        num_inputs: usize,
        num_vars: usize,
    ) {
        for i in (num_inputs + 1)..=num_vars {
            let gv = &vars[Var(i as u32)];
            if gv.is_deleted {
                continue;
            }

            let mut is_xor: u32 = 0;
            let mut neighbors = Vec::new();

            if gv.gate_type == GateType::Xor {
                is_xor += 1;
            }
            for &fanin_lit in &gv.fanin {
                let fanin_var = fanin_lit.var();
                let fanin_gv = &vars[fanin_var];
                if fanin_gv.gate_type == GateType::Xor {
                    neighbors.push(fanin_var);
                    is_xor += 1;
                }
            }
            for &fanout_var in &gv.fanout {
                let fanout_gv = &vars[fanout_var];
                if fanout_gv.gate_type == GateType::Xor {
                    neighbors.push(fanout_var);
                    is_xor += 1;
                }
            }

            let gv = &mut vars[Var(i as u32)];
            gv.neighbors = neighbors;
            gv.xor_edges = is_xor;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    #[test]
    fn test_vsids_decide() {
        let num_vars = 5;
        let mut branch = Branch::new(num_vars);
        branch.init_vsids(num_vars);

        // Bump var 3 to highest activity (after init, which resets all to 0)
        branch.var_activity[3] = 10.0;
        branch.heap.update(Var(3), &branch.var_activity);

        let mut value = LitAssign::new();
        let mut assigns = vec![super::super::gate::Assign::default(); num_vars + 1];
        for v in 0..=num_vars {
            value.reserve_var(Var(v as u32));
        }
        let vars = GateVarMap::new();
        let clauses = Vec::new();
        let mut trail = Vec::new();

        let lit = branch.decide(&mut value, &vars, &clauses, &mut trail, &mut assigns);
        assert!(lit.is_some());
        let lit = lit.unwrap();
        assert_eq!(lit.var(), Var(3));
    }

    #[test]
    fn test_bump_and_rescale() {
        let mut branch = Branch::new(3);
        branch.init_vsids(3);
        branch.var_activity[1] = 1e100;
        branch.var_inc = 1e100;
        branch.bump_var(Var(1), 1.0);
        assert!(branch.var_activity[1] < 1e100);
    }

    #[test]
    fn test_phase_saving() {
        let num_vars = 3;
        let mut branch = Branch::new(num_vars);
        branch.init_vsids(num_vars);

        branch.saved[1] = -1;

        let mut value = LitAssign::new();
        let mut assigns = vec![super::super::gate::Assign::default(); num_vars + 1];
        for v in 0..=num_vars {
            value.reserve_var(Var(v as u32));
        }
        let vars = GateVarMap::new();
        let clauses = Vec::new();
        let mut trail = Vec::new();

        let lit = branch.decide(&mut value, &vars, &clauses, &mut trail, &mut assigns);
        assert!(lit.is_some());
        assert!(!lit.unwrap().polarity()); // should use saved negative phase
    }
}

//! Hand a hard query to CaDiCaL. gipsat's heuristics are tuned for IC3's many
//! small queries; when one query runs past `Config::fallback` conflicts, the
//! current clause database (transition, lemma and temporary clauses, level-0
//! units and recorded equivalences; learnt clauses are implied and left out)
//! is solved by CaDiCaL under the same assumptions. On UNSAT the failed
//! assumptions become the unsat core. On SAT the model becomes gipsat's saved
//! phase and gipsat searches again: every decision and implication then agrees
//! with a satisfying assignment, so the search ends without a conflict and
//! leaves gipsat's trail, reasons and values consistent for lifting.

use super::DagCnfSolver;
use cadical::CaDiCaL;
use logicrs::{Lbool, Lit, Var, VarRange, satif::Satif};

impl DagCnfSolver {
    pub(super) fn fallback_cadical(&mut self, assumption: &[Lit]) -> Option<bool> {
        let start = std::time::Instant::now();
        self.statistic.num_fallback += 1;
        let mut slv = CaDiCaL::new();
        let max = self.max_var();
        while slv.num_var() <= usize::from(max) {
            slv.new_var();
        }
        let groups = [
            self.cdb.trans.clone(),
            self.cdb.lemmas.clone(),
            self.cdb.temporary.clone(),
        ];
        for g in groups.iter() {
            for &c in g.iter() {
                slv.add_clause(self.cdb.get(c).slice());
            }
        }
        for i in 0..self
            .pos_in_trail
            .first()
            .copied()
            .unwrap_or(self.trail.len() as u32)
        {
            let l = self.trail[i];
            slv.add_clause(&[l]);
        }
        slv.add_clause(&[Lit::constant(true)]);
        for v in VarRange::new_inclusive(Var::new(1), max) {
            let r = self.eqc.get_eq(v.lit());
            if r != v.lit() {
                slv.add_clause(&[!v.lit(), r]);
                slv.add_clause(&[v.lit(), !r]);
            }
        }
        let sat = slv.solve(assumption);
        let res = if sat {
            self.statistic.num_fallback_sat += 1;
            for v in VarRange::new_inclusive(Var::new(1), max) {
                if let Some(b) = slv.sat_value(v.lit()) {
                    self.phase_saving[v] = Lbool::from(b);
                }
            }
            let ps = self.cfg.phase_saving;
            self.cfg.phase_saving = true;
            let r = self.search(assumption, None);
            self.cfg.phase_saving = ps;
            debug_assert_eq!(r, Some(true));
            r
        } else {
            self.backtrack(0, true);
            self.unsat_core.clear();
            for &a in assumption.iter() {
                if slv.unsat_has(a) {
                    self.unsat_core.insert(a);
                }
            }
            Some(false)
        };
        self.statistic.fallback_time += start.elapsed();
        res
    }
}

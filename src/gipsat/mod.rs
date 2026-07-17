mod analyze;
mod cdb;
mod domain;
mod eq;
mod propagate;
mod search;
mod simplify;
mod statistic;
mod ts;
mod vsids;

use crate::gipsat::eq::Eqc;
use analyze::Analyze;
pub use cdb::ClauseKind;
use cdb::{CREF_NONE, CRef, ClauseDB};
use domain::Domain;
use giputils::bitvec::BitVec;
use giputils::gvec::Gvec;
use giputils::ptr::Gptr;
use logicrs::satif::Satif;
use logicrs::{DagCnf, Lbool, VarAssign, VarRange};
use logicrs::{Lit, LitSet, LitVec, Var, VarMap};
use propagate::Watchers;
use rand::RngExt;
use rand::{SeedableRng, rngs::SmallRng};
use simplify::Simplify;
pub use statistic::SolverStatistic;
use std::iter::empty;
use std::time::Instant;
pub use ts::*;
use vsids::Vsids;

#[derive(Clone)]
pub struct DagCnfSolver {
    cdb: ClauseDB,
    watchers: Watchers,
    value: VarAssign,
    trail: Gvec<Lit>,
    pos_in_trail: Vec<u32>,
    level: VarMap<u32>,
    reason: VarMap<CRef>,
    propagated: u32,
    vsids: Vsids,
    phase_saving: VarMap<Lbool>,
    analyze: Analyze,
    simplify: Simplify,
    eqc: Eqc,
    unsat_core: LitSet,
    domain: Domain,
    temporary_domain: bool,
    prepared_vsids: bool,
    constrain_act: Var,
    dc: Gptr<DagCnf>,
    trivial_unsat: bool,
    mark: LitSet,
    rng: SmallRng,
    pub cfg: Config,

    assump: LitVec,
    constraint: Vec<LitVec>,

    /// ILB (incremental lazy backtracking): reuse the trail prefix shared with
    /// the previous solve instead of backtracking to level 0 on every query.
    ilb: bool,
    /// also reuse after SAT results (requires restoring trail/value coherence)
    ilb_sat: bool,
    /// debug: re-solve every fast-path query via full reset and compare
    ilb_check: bool,
    /// full assumption vector of the previous solve (including the constraint
    /// activation literal, which is placed last)
    last_assump: Option<LitVec>,
    /// result of the previous solve; None (limit hit / state reset) disables
    /// the fast path. After SAT, model shrinking (flip_to_none) may have set
    /// trail literals' values to none — restored before reuse.
    last_res: Option<bool>,
    /// set by conflict analysis when the derivation resolved through the
    /// constraint activation variable: the learnt then depends on this
    /// round's temporary clauses and must not outlive them
    saw_act_resolution: bool,
    /// watch pairs mutated by model shrinking (flip_to_none) since the last
    /// solve. Master re-propagates from scratch each solve, so mutated
    /// watches are harmless there; a reused trail keeps values whose watch
    /// structure these mutations broke — replayed in reverse before reuse
    pub(crate) flip_undo: Vec<(CRef, [Lit; 2])>,
    /// the current model came from a fast-path (trail-reusing) solve: model
    /// shrinking must be conservative, since flip feasibility reasoning
    /// assumes a watch structure established by a from-scratch propagation
    model_from_fast: bool,

    statistic: SolverStatistic,
}

#[derive(Debug, Clone)]
pub struct Config {
    pub phase_saving: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self { phase_saving: true }
    }
}

impl DagCnfSolver {
    pub fn new(dc: &DagCnf) -> Self {
        let constrain_act = Var::CONST;
        let mut solver = Self {
            dc: Gptr::new(dc),
            cdb: Default::default(),
            watchers: Default::default(),
            value: VarAssign::new_with(constrain_act),
            trail: Default::default(),
            pos_in_trail: Default::default(),
            level: VarMap::new_with(constrain_act),
            reason: VarMap::new_with(constrain_act),
            propagated: Default::default(),
            vsids: Default::default(),
            phase_saving: Default::default(),
            analyze: Default::default(),
            simplify: Default::default(),
            eqc: Default::default(),
            unsat_core: Default::default(),
            domain: Domain::new(),
            temporary_domain: Default::default(),
            prepared_vsids: false,
            constrain_act,
            assump: Default::default(),
            constraint: Default::default(),
            statistic: Default::default(),
            trivial_unsat: false,
            rng: SmallRng::seed_from_u64(0),
            cfg: Default::default(),
            mark: Default::default(),
            ilb: std::env::var("GIPSAT_ILB").map(|v| v != "0").unwrap_or(true),
            ilb_sat: std::env::var("GIPSAT_ILB_SAT").map(|v| v != "0").unwrap_or(true),
            ilb_check: std::env::var("GIPSAT_ILB_CHECK").map(|v| v != "0").unwrap_or(false),
            flip_undo: Vec::new(),
            model_from_fast: false,
            last_assump: None,
            last_res: None,
            saw_act_resolution: false,
        };
        while solver.num_var() < solver.dc.num_var() {
            solver.new_var();
        }
        for cls in dc.clause() {
            solver.add_clause_inner(cls, ClauseKind::Trans);
        }
        assert!(solver.propagate() == CREF_NONE);
        solver
    }

    #[inline]
    #[allow(unused)]
    pub fn set_rseed(&mut self, rseed: u64) {
        self.rng = SmallRng::seed_from_u64(rseed);
    }

    fn simplify_clause(&mut self, clause: &[Lit]) -> Option<LitVec> {
        assert!(self.highest_level() == 0);
        let mut clause = logicrs::LitVec::from(clause);
        clause.sort();
        let clause = clause.ordered_simp(&self.value)?;
        if clause.is_empty() {
            self.trivial_unsat = true;
            return None;
        }
        Some(clause)
    }

    fn add_clause_inner(&mut self, clause: &[Lit], mut kind: ClauseKind) -> CRef {
        if let Some(clause) = self.simplify_clause(clause) {
            if clause.iter().any(|l| l.var() == self.constrain_act) {
                kind = ClauseKind::Temporary;
            }
            if clause.len() == 1 {
                assert!(clause[0].var() != self.constrain_act);
                match self.value.v(clause[0]) {
                    Lbool::TRUE | Lbool::FALSE => todo!(),
                    _ => {
                        self.assign(clause[0], CREF_NONE);
                        if self.propagate() != CREF_NONE {
                            self.trivial_unsat = true;
                        }
                        CREF_NONE
                    }
                }
            } else {
                self.attach_clause(&clause, kind)
            }
        } else {
            CREF_NONE
        }
    }

    pub fn add_eq(&mut self, x: Lit, y: Lit) {
        self.eqc.add_eq(x, y);
    }

    fn reset(&mut self) {
        self.backtrack(0, false);
        self.clean_temporary();
        self.prepared_vsids = false;
        self.domain.reset();
        self.last_assump = None;
        self.last_res = None;
        assert!(!self.temporary_domain);
    }

    /// Length of the trail-prefix (in decision levels) reusable from the
    /// previous solve, or 0 if the fast path does not apply.
    fn ilb_target(&mut self, assumption: &LitVec) -> usize {
        if !self.ilb
            || self.temporary_domain
            || self.last_res.is_none()
            || (self.last_res == Some(true) && !self.ilb_sat)
            || self.highest_level() == 0
            || assumption.is_empty()
        {
            return 0;
        }
        let Some(last) = self.last_assump.as_ref() else {
            return 0;
        };
        // assumptions are placed one per decision level, so level k holds
        // assumption k-1; identical prefixes yield identical trail structure.
        // Capping at last.len() also guarantees that after a SAT result only
        // assumption levels (whose literals are implications of the formula
        // and the shared prefix) are kept — free search decisions above them
        // are never reused.
        let max = last
            .len()
            .min(assumption.len().saturating_sub(1))
            .min(self.highest_level());
        let mut target = 0;
        while target < max && last[target] == assumption[target] {
            target += 1;
        }
        // never reuse the activation literal's level: temporary clauses are
        // replaced between queries
        while target > 0 && assumption[target - 1].var() == self.constrain_act {
            target -= 1;
        }
        let prefix = target;
        // the previous round may have propagated ¬act below the target through
        // a temporary clause; those levels cannot be kept
        if target > 0 && !self.value.v(self.constrain_act.lit()).is_none() {
            let la = self.level[self.constrain_act] as usize;
            if la <= target {
                target = la.saturating_sub(1);
                self.statistic.num_ilb_clamp_act += 1;
            }
        }
        // temporary clauses (including act-free learnts quarantined by
        // saw_act_resolution) may be reasons of kept literals; clamp below any
        // such assignment so detaching them leaves no dangling reason
        let mut clamped_locked = false;
        for &t in self.cdb.temporary.iter() {
            if target == 0 {
                break;
            }
            if self.locked(t) {
                let lv = self.level[self.cdb.get(t)[0]] as usize;
                if lv <= target {
                    target = lv.saturating_sub(1);
                    clamped_locked = true;
                }
            }
        }
        if clamped_locked {
            self.statistic.num_ilb_clamp_locked += 1;
        }
        if prefix > 0 {
            self.statistic.avg_ilb_prefix += prefix as f64;
        }
        target
    }

    /// Restore trail coherence after model shrinking. flip_to_none (a) sets
    /// values of trail literals to none without popping them, and (b) may
    /// permute the literals of a clause that is the *reason* of a trail
    /// literal while re-watching, breaking the invariant that the propagated
    /// literal sits at index 0 — which conflict analysis relies on. Reusing a
    /// trail without repairing both would let analyze derive unsound learnts.
    fn restore_trail_coherence(&mut self) {
        let start = Instant::now();
        self.statistic.num_flip_replay += self.flip_undo.len();
        for i in 0..self.trail.len() {
            let p = self.trail[i];
            if self.value.v(p).is_none() {
                self.value.set(p);
            }
        }
        // undo watch mutations from model shrinking, newest first, so the
        // watch structure again matches the (restored) propagation fixpoint
        while let Some((cid, w)) = self.flip_undo.pop() {
            let c = self.cdb.get(cid);
            if c.is_removed() {
                continue;
            }
            self.watchers.detach(cid, c);
            let mut c = self.cdb.get(cid);
            let p0 = (0..c.len()).find(|&j| c[j] == w[0]).unwrap();
            c.swap(0, p0);
            let p1 = (1..c.len()).find(|&j| c[j] == w[1]).unwrap();
            c.swap(1, p1);
            self.watchers.attach(cid, c);
        }
        // belt and braces: conflict analysis requires reason[0] == the
        // propagated literal
        for i in 0..self.trail.len() {
            let p = self.trail[i];
            let r = self.reason[p];
            if r != CREF_NONE {
                let c = self.cdb.get(r);
                if c[0] != p {
                    let pos = (0..c.len()).find(|&j| c[j] == p).unwrap();
                    self.watchers.detach(r, c);
                    let mut c = self.cdb.get(r);
                    c.swap(0, pos);
                    self.watchers.attach(r, c);
                }
            }
        }
        self.statistic.restore_time += start.elapsed();
    }

    /// Detach this round's temporary clauses. Unlike `clean_temporary`, this
    /// assumes no kept trail literal has a temporary reason (guaranteed by
    /// `ilb_target`) and the activation variable is unassigned.
    fn detach_temporaries(&mut self) {
        debug_assert!(self.value.v(self.constrain_act.lit()).is_none());
        while let Some(t) = self.cdb.temporary.pop() {
            self.detach_clause(t);
        }
    }

    /// Attach a temporary constraint clause while the trail is at a non-zero
    /// level. The clause must contain ¬act (unassigned here), so at least one
    /// watchable literal always exists; if the clause is unit under the kept
    /// trail, ¬act is propagated with the clause as reason.
    fn attach_temporary_at_level(&mut self, mut c: LitVec) {
        debug_assert!(self.value.v(self.constrain_act.lit()).is_none());
        c.sort();
        let mut dst = 1;
        for i in 1..c.len() {
            if c[i] == c[dst - 1] {
                continue;
            }
            if c[i].var() == c[dst - 1].var() {
                // tautology: always satisfied, no constraint to add
                return;
            }
            c[dst] = c[i];
            dst += 1;
        }
        c.truncate(dst);
        let mut w0 = None;
        let mut w1 = None;
        for (i, l) in c.iter().enumerate() {
            if !self.value.v(*l).is_false() {
                if w0.is_none() {
                    w0 = Some(i);
                } else {
                    w1 = Some(i);
                    break;
                }
            }
        }
        let w0 = w0.unwrap();
        c.swap(0, w0);
        if let Some(w1) = w1 {
            debug_assert!(w1 > w0);
            c.swap(1, w1);
            self.attach_clause(&c, ClauseKind::Temporary);
        } else {
            // unit: the only non-false literal must be ¬act
            debug_assert!(c[0] == !self.constrain_act.lit());
            if c.len() == 1 {
                self.assign(c[0], CREF_NONE);
            } else {
                // watch the highest-level false literal so backtracking
                // re-wakes the clause correctly
                let mut best = 1;
                for i in 2..c.len() {
                    if self.level[c[i]] > self.level[c[best]] {
                        best = i;
                    }
                }
                c.swap(1, best);
                let cref = self.attach_clause(&c, ClauseKind::Temporary);
                self.assign(c[0], cref);
            }
        }
    }

    fn prepare_round(
        &mut self,
        assumption: &LitVec,
        constraint: Vec<LitVec>,
        domain: impl Iterator<Item = Var>,
        bucket: bool,
    ) -> bool {
        if self.ilb && self.ilb_sat && self.last_res == Some(true) {
            // model shrinking may have decoupled values/reasons/watches from
            // the trail; restore coherence before deciding on (and using) reuse
            self.restore_trail_coherence();
        }
        self.flip_undo.clear();
        let target = self.ilb_target(assumption);
        if target == 0 {
            // ----- full reset (original) path -----
            self.backtrack(0, self.temporary_domain);
            self.clean_temporary();
            self.prepared_vsids = false;

            for mut c in constraint {
                c.push(!self.constrain_act.lit());
                if let Some(c) = self.simplify_clause(&c) {
                    assert!(!c.is_empty());
                    if c.len() == 1 {
                        return false;
                    }
                    self.add_clause_inner(&c, ClauseKind::Temporary);
                }
            }

            if !self.temporary_domain {
                self.domain.enable_local(domain, &self.dc, &self.value);
                assert!(!self.domain.has(self.constrain_act));
                self.domain.insert(self.constrain_act);
                if bucket {
                    self.vsids.enable_bucket = true;
                    self.vsids.bucket.clear();
                } else {
                    self.vsids.enable_bucket = false;
                    self.vsids.heap.clear();
                }
            }
        } else {
            // ----- ILB fast path: keep the shared assumption prefix -----
            self.statistic.num_ilb += 1;
            self.statistic.avg_ilb_reuse += target as f64;
            let constrained = !assumption.is_empty()
                && assumption[assumption.len() - 1].var() == self.constrain_act;
            if constrained {
                self.statistic.num_ilb_con += 1;
                self.statistic.avg_ilb_reuse_con += target as f64;
                self.statistic.avg_ilb_frac_con +=
                    target as f64 / (assumption.len() - 1).max(1) as f64;
            } else {
                self.statistic.avg_ilb_reuse_unc += target as f64;
            }
            self.backtrack(target, false);
            self.detach_temporaries();
            self.prepared_vsids = false;
            for mut c in constraint {
                c.push(!self.constrain_act.lit());
                self.attach_temporary_at_level(c);
            }
            self.domain.enable_local(domain, &self.dc, &self.value);
            assert!(!self.domain.has(self.constrain_act));
            self.domain.insert(self.constrain_act);
            self.vsids.enable_bucket = true;
            self.vsids.bucket.clear();
            if std::env::var("GIPSAT_ILB_AUDIT").is_ok() {
                for i in 0..self.trail.len() {
                    let p = self.trail[i];
                    assert!(self.value.v(p).is_true(), "kept trail lit {p:?} not true");
                    // level-0 reasons are never dereferenced (analysis skips
                    // level-0 literals) and may legitimately dangle
                    if self.level[p] == 0 {
                        continue;
                    }
                    let r = self.reason[p];
                    if r != CREF_NONE {
                        let c = self.cdb.get(r);
                        assert!(c[0] == p, "kept reason[0] != lit for {p:?}");
                        assert!(!c.is_removed(), "kept reason removed for {p:?}");
                        for j in 1..c.len() {
                            assert!(
                                self.value.v(c[j]).is_false(),
                                "kept reason of {p:?} has non-false lit {:?} at {j}",
                                c[j]
                            );
                        }
                    }
                }
            }
        }
        let free = self.dc.num_var().saturating_sub(self.trail.len());
        if free > 0 {
            self.statistic.avg_decide_var += self.domain.len() as f64 / free as f64;
        }
        true
    }

    pub fn solve_with_param(
        &mut self,
        assump: &[Lit],
        constraint: Vec<LitVec>,
        domain: impl Iterator<Item = Var>,
        limit: Option<usize>,
    ) -> Option<bool> {
        self.assump = assump.into();
        self.constraint = constraint.clone();
        if self.trivial_unsat {
            self.unsat_core.clear();
            return Some(false);
        }
        self.statistic.num_solve += 1;
        let start = Instant::now();
        if self.propagate() != CREF_NONE {
            self.trivial_unsat = true;
            self.unsat_core.clear();
            self.last_res = None;
            self.statistic.avg_solve_time += start.elapsed();
            return Some(false);
        }
        // full assumption vector; the constraint activation literal goes LAST
        // so that the shared assumption prefix sits at the bottom of the trail
        // and survives temporary-clause replacement across queries (ILB)
        let mut assumption = LitVec::from(assump);
        if !constraint.is_empty() {
            assumption.push(self.constrain_act.lit());
        }
        let dvars: Vec<Var> = domain
            .chain(assump.iter().map(|l| l.var()))
            .chain(constraint.iter().flatten().map(|l| l.var()))
            .collect();
        let num_ilb_before = self.statistic.num_ilb;
        if !self.prepare_round(&assumption, constraint, dvars.iter().copied(), true) {
            self.unsat_core.clear();
            self.last_assump = Some(assumption);
            self.last_res = Some(false);
            self.statistic.avg_solve_time += start.elapsed();
            return Some(false);
        }
        if self.highest_level() == 0 {
            // level-0 maintenance is only possible on full-reset rounds
            self.clean_learnt(true);
            self.simplify();
        }
        let mut res = self.search_with_restart(&assumption, limit);
        if res == Some(true)
            && self.statistic.num_ilb > num_ilb_before
            && std::env::var("GIPSAT_ILB_VERIFY").is_ok()
        {
            assert!(
                self.verify(&assumption),
                "ILB fast-path SAT model failed verification"
            );
        }
        if self.ilb_check && self.statistic.num_ilb > num_ilb_before {
            // re-solve from scratch and compare: the clause database now also
            // holds the fast solve's learnts, but that cannot change the answer
            let fast_res = res;
            self.last_res = None; // force the slow path
            let ok = self.prepare_round(
                &assumption,
                self.constraint.clone(),
                dvars.iter().copied(),
                true,
            );
            res = if ok {
                self.clean_learnt(true);
                self.simplify();
                self.search_with_restart(&assumption, limit)
            } else {
                self.unsat_core.clear();
                Some(false)
            };
            assert_eq!(
                fast_res, res,
                "ILB divergence: fast={fast_res:?} slow={res:?} assump={assumption:?}"
            );
        }
        self.last_assump = Some(assumption);
        self.last_res = res;
        self.model_from_fast = res == Some(true) && self.statistic.num_ilb > num_ilb_before;
        self.statistic.avg_solve_time += start.elapsed();
        res
    }

    pub fn solve_with_restart_limit(
        &mut self,
        assumps: &[Lit],
        constraint: Vec<LitVec>,
        limit: usize,
    ) -> Option<bool> {
        self.solve_with_param(assumps, constraint, empty::<Var>(), Some(limit))
    }

    pub fn solve_with_domain(
        &mut self,
        assumps: &[Lit],
        domain: impl Iterator<Item = Var>,
    ) -> bool {
        self.solve_with_param(assumps, vec![], domain, None)
            .unwrap()
    }

    #[allow(unused)]
    pub fn imply<'a>(
        &mut self,
        domain: impl Iterator<Item = Var>,
        assump: impl Iterator<Item = &'a Lit>,
    ) {
        self.reset();
        self.domain.enable_local(domain, &self.dc, &self.value);
        self.new_level();
        for a in assump {
            if let Lbool::FALSE = self.value.v(*a) {
                panic!();
            }
            self.assign(*a, CREF_NONE);
        }
        assert!(self.propagate() == CREF_NONE);
    }

    #[inline]
    #[allow(unused)]
    pub fn assert_value(&mut self, lit: Lit) -> Option<bool> {
        self.reset();
        self.value.v(lit).into()
    }

    #[inline]
    pub fn statistic(&self) -> &SolverStatistic {
        &self.statistic
    }

    #[allow(unused)]
    pub fn sat_value_bitvet(&mut self) -> BitVec {
        let mut res = BitVec::new();
        for v in VarRange::new_inclusive(Var::CONST, self.max_var()) {
            if let Some(v) = self.sat_value(v.lit()) {
                res.push(v);
            } else {
                res.push(self.rng.random_bool(0.5));
            }
        }
        res
    }

    #[allow(unused)]
    pub fn sat_value_iter(&self) -> impl Iterator<Item = &'_ Lit> {
        let constrain_act = self.constrain_act;
        self.trail.iter().filter(move |l| l.var() != constrain_act)
    }

    pub fn minimal_premise(
        &mut self,
        assump: &[Lit],
        premise: &[Lit],
        consequent: &[Lit],
    ) -> Option<LitVec> {
        let assump = LitVec::from_iter(assump.iter().chain(premise.iter()).copied());
        if self.solve_with_constraint(&assump, vec![LitVec::from(consequent)]) {
            return None;
        }
        Some(
            premise
                .iter()
                .filter(|l| self.unsat_has(**l))
                .copied()
                .collect(),
        )
    }
}

impl Satif for DagCnfSolver {
    #[inline]
    fn new_var(&mut self) -> Var {
        self.reset();
        let v = self.constrain_act;
        let var = Var::new(self.num_var() + 1);
        self.value.reserve(var);
        self.level.reserve(var);
        self.reason.reserve(var);
        self.watchers.reserve(var);
        self.vsids.reserve(var);
        self.phase_saving.reserve(var);
        self.eqc.reserve(var);
        self.analyze.reserve(var);
        self.unsat_core.reserve(var);
        self.domain.reserve(var);
        self.mark.reserve(var);
        self.constrain_act = var;
        v
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.constrain_act.into()
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        self.reset();
        for l in clause.iter() {
            self.add_domain(l.var(), true);
        }
        self.add_clause_inner(clause, ClauseKind::Lemma);
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        self.solve_with_param(assumps, vec![], empty::<Var>(), None)
            .unwrap()
    }

    fn solve_with_constraint(&mut self, assumps: &[Lit], constraint: Vec<LitVec>) -> bool {
        self.solve_with_param(assumps, constraint, empty::<Var>(), None)
            .unwrap()
    }

    #[inline]
    fn sat_value(&self, lit: Lit) -> Option<bool> {
        match self.value.v(lit) {
            Lbool::TRUE => Some(true),
            Lbool::FALSE => Some(false),
            _ => None,
        }
    }

    #[inline]
    fn unsat_has(&self, lit: Lit) -> bool {
        self.unsat_core.has(lit)
    }

    #[inline]
    fn flip_to_none(&mut self, var: Var) -> bool {
        self.flip_to_none_inner(var)
    }
}

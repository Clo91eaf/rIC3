use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef, ClauseKind},
};
use log::debug;
use logicrs::Var;
use logicrs::{Lbool, Lit};

impl DagCnfSolver {
    #[inline]
    pub fn highest_level(&self) -> usize {
        self.pos_in_trail.len()
    }

    #[inline]
    pub fn assign(&mut self, lit: Lit, reason: CRef) {
        self.trail.push(lit);
        self.value.set(lit);
        self.reason[lit] = reason;
        self.level[lit] = self.highest_level() as u32;
    }

    #[inline]
    pub fn new_level(&mut self) {
        self.pos_in_trail.push(self.trail.len() as u32)
    }

    #[inline]
    pub fn backtrack(&mut self, level: usize, vsids: bool) {
        if self.highest_level() <= level {
            return;
        }
        while self.trail.len() as u32 > self.pos_in_trail[level] {
            let bt = self.trail.pop().unwrap();
            self.value.set_none(bt.var());
            if vsids {
                self.vsids.push(bt.var());
            }
            self.phase_saving[bt] = Lbool::from(bt.polarity());
        }
        self.propagated = self.pos_in_trail[level];
        self.pos_in_trail.truncate(level);
    }

    pub fn search_with_restart(
        &mut self,
        assumption: &[Lit],
        limit: Option<usize>,
    ) -> Option<bool> {
        let mut restarts = 0;
        loop {
            if let Some(limit) = limit
                && restarts >= limit as u32
            {
                return None;
            }
            if restarts > 10 && self.vsids.enable_bucket {
                self.vsids.enable_bucket = false;
                self.vsids.heap.clear();
                for d in self.domain.iter() {
                    if self.value.v(d.lit()).is_none() {
                        self.vsids.push(*d);
                    }
                }
            }
            let rest_base = luby(2.0, restarts);
            match self.search(assumption, Some(rest_base * 100.0)) {
                None => {
                    restarts += 1;
                    if restarts % 10 == 0 {
                        debug!(
                            "gipsat restarted {restarts} times with {} learnt clauses",
                            self.cdb.num_learnt()
                        );
                    }
                }
                Some(r) => return Some(r),
            }
        }
    }

    pub fn search(&mut self, assumption: &[Lit], noc: Option<f64>) -> Option<bool> {
        let mut num_conflict = 0.0_f64;
        'ml: loop {
            let conflict = self.propagate();
            if conflict != CREF_NONE {
                num_conflict += 1.0;
                if self.highest_level() == 0 {
                    self.unsat_core.clear();
                    return Some(false);
                }
                let (learnt, btl) = self.analyze(conflict);
                self.backtrack(btl, true);
                if learnt.len() == 1 {
                    debug_assert!(btl == 0);
                    self.assign(learnt[0], CREF_NONE);
                } else {
                    let mut kind = ClauseKind::Learnt;
                    for l in learnt.iter() {
                        if self.constrain_act == l.var() {
                            kind = ClauseKind::Temporary;
                        }
                    }
                    let learnt_id = self.attach_clause(&learnt, kind);
                    self.cdb.bump(learnt_id);
                    let assign = self.cdb.get(learnt_id)[0];
                    self.assign(assign, learnt_id);
                }
                self.vsids.decay();
                self.cdb.decay();
                // Method 1: periodic re-boost
                self.conflict_count += 1;
                if self.hint_reboost_interval > 0
                    && self.conflict_count % self.hint_reboost_interval == 0
                {
                    for var_idx in 0..self.hint_init_activity.len() {
                        let var = Var::new(var_idx);
                        let init = self.hint_init_activity[var];
                        if init > 0.0 && self.vsids.activity[var] < init {
                            self.vsids.activity.set(var, init);
                        }
                    }
                }
                // Method 3: slower decay for hinted vars (compensate the global decay)
                if self.hint_decay_factor < 1.0 {
                    for var_idx in 0..self.hinted_vars.len() {
                        let var = Var::new(var_idx);
                        if self.hinted_vars[var] {
                            // Partially undo the decay: multiply by 1/decay^(1-factor)
                            // factor=0.5 means hinted vars decay at half the rate
                            let compensation = 1.0 / f64::powf(0.95, 1.0 - self.hint_decay_factor);
                            self.vsids.activity.boost(var, compensation);
                        }
                    }
                }
            } else {
                if let Some(noc) = noc
                    && num_conflict >= noc
                {
                    self.backtrack(assumption.len(), true);
                    return None;
                }
                self.clean_learnt(false);
                while self.highest_level() < assumption.len() {
                    let a = assumption[self.highest_level()];
                    match self.value.v(a) {
                        Lbool::TRUE => {
                            self.new_level();
                            if self.highest_level() == assumption.len() {
                                self.prepare_vsids();
                            }
                        }
                        Lbool::FALSE => {
                            self.analyze_unsat_core(a);
                            return Some(false);
                        }
                        _ => {
                            self.new_level();
                            self.assign(a, CREF_NONE);
                            if self.highest_level() == assumption.len() {
                                self.prepare_vsids();
                            }
                            continue 'ml;
                        }
                    }
                }
                if !self.decide() {
                    return Some(true);
                }
            }
        }
    }
}

fn luby(y: f64, mut x: u32) -> f64 {
    let mut size = 1;
    let mut seq = 0;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq)
}

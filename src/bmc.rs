use crate::{
    Engine, McResult, McWitness,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    impl_config_deref,
    structhint::{SignalType, StructHint},
    tracer::{Tracer, TracerIf},
    transys::{Transys, TransysIf, certify::Restore, nodep::NoDepTransys, unroll::TransysUnroll},
};
use clap::{Args, Parser};
use log::info;
use logicrs::{Lit, LitVec, satif::Satif};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct BMCConfig {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// per-step time limit (applies to each BMC step, not the overall solver run).
    /// The overall `time_limit` option sets the total time limit for the entire solver run.
    #[arg(long = "step-time-limit")]
    pub step_time_limit: Option<u64>,

    /// use kissat solver in bmc, otherwise cadical
    #[arg(long = "kissat", default_value_t = false)]
    pub kissat: bool,

    /// dynamic step
    #[arg(long = "dyn-step", default_value_t = false)]
    pub dyn_step: bool,

    /// Hint-guided adaptive step: adjust BMC step size based on control-variable
    /// density in the hint. Higher control density → smaller steps.
    #[arg(long = "hint-adaptive-step", default_value_t = false)]
    pub hint_adaptive_step: bool,

    /// Hint-guided soft constraints: inject activation-guarded clauses that bias
    /// the solver toward exploring control-variable assignments first.
    #[arg(long = "hint-guide", default_value_t = false)]
    pub hint_guide: bool,
}

impl_config_deref!(BMCConfig);

impl Default for BMCConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "bmc"]);
        cfg.into_bmc().unwrap()
    }
}

pub struct BMC {
    ots: Transys,
    uts: TransysUnroll<NoDepTransys>,
    cfg: BMCConfig,
    solver: Box<dyn Satif>,
    solver_k: usize,
    rst: Restore,
    step: usize,
    rng: StdRng,
    tracer: Tracer,
    struct_hint: Option<StructHint>,
    /// Activation literals for hint-guide soft constraints, one per unrolled step.
    guide_acts: Vec<Lit>,
}

impl BMC {
    pub fn new(cfg: BMCConfig, mut ts: Transys, struct_hint: Option<StructHint>) -> Self {
        let ots = ts.clone();
        ts.compress_bads();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let rst = Restore::new(&ts);
        let (ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        if cfg.preproc.preproc {
            ts.simplify(&mut rst);
        }
        let uts = TransysUnroll::new(&ts);
        let mut solver: Box<dyn Satif> = if cfg.kissat {
            Box::new(kissat::Kissat::new())
        } else {
            Box::new(cadical::CaDiCaL::new())
        };
        solver.set_seed(rng.random());
        ts.load_init(solver.as_mut());

        let step = if cfg.hint_adaptive_step {
            Self::compute_adaptive_step(&struct_hint, &uts.ts, cfg.step as usize)
        } else if cfg.dyn_step {
            (10_000_000 / (*ts.max_var() as usize + ts.rel.clauses().len())).max(1)
        } else {
            cfg.step as usize
        };

        if let Some(ref hint) = struct_hint {
            info!(
                "StructHint loaded for BMC: {} hints, adaptive_step={}, guide={}",
                hint.len(),
                cfg.hint_adaptive_step,
                cfg.hint_guide
            );
        }

        Self {
            ots,
            uts,
            step,
            cfg,
            solver,
            solver_k: 0,
            rst,
            rng,
            tracer: Tracer::new(),
            struct_hint,
            guide_acts: Vec::new(),
        }
    }

    /// Compute adaptive step size from control-variable density in hints.
    ///
    /// High control density → property depends on short control paths → small steps.
    /// Low control density → mostly datapath → larger steps to reach deeper states.
    fn compute_adaptive_step(
        hint: &Option<StructHint>,
        ts: &NoDepTransys,
        default_step: usize,
    ) -> usize {
        let hint = match hint {
            Some(h) if !h.is_empty() => h,
            _ => return default_step,
        };

        let total_latches = ts.latch.len();
        if total_latches == 0 {
            return default_step;
        }

        let control_count = ts
            .latch
            .iter()
            .filter(|v| matches!(hint.get(**v), Some(SignalType::Control)))
            .count();

        let density = control_count as f64 / total_latches as f64;

        let step = if density >= 0.3 {
            1
        } else if density >= 0.1 {
            2
        } else if density >= 0.01 {
            5
        } else {
            10
        };

        info!(
            "BMC adaptive step: {}/{} latches are control ({:.1}% density) -> step={}",
            control_count, total_latches, density * 100.0, step
        );
        step
    }

    pub fn load_trans_to(&mut self, k: usize) {
        while self.solver_k < k + 1 {
            self.uts
                .load_trans(self.solver.as_mut(), self.solver_k, true);
            self.solver_k += 1;
        }
    }

    pub fn reset_solver(&mut self) {
        self.solver = if self.cfg.kissat {
            Box::new(kissat::Kissat::new())
        } else {
            Box::new(cadical::CaDiCaL::new())
        };
        self.solver.set_seed(self.rng.random());
        self.uts.ts.load_init(self.solver.as_mut());
        for i in 0..self.solver_k {
            self.uts.load_trans(self.solver.as_mut(), i, true);
        }
        if self.cfg.hint_guide {
            self.guide_acts.clear();
            if let Some(hint) = self.struct_hint.clone() {
                for step in 0..self.solver_k {
                    self.inject_guide_constraints(hint.clone(), step);
                }
            }
        }
    }

    /// Inject soft constraints for control variables at unrolled time step.
    ///
    /// For each control-type latch at step k, adds: act_k -> control_var_at_k
    /// When act_k is assumed true, the solver is biased toward positive polarity
    /// for control variables. If this leads to UNSAT, act_k is dropped.
    fn inject_guide_constraints(&mut self, hint: StructHint, step: usize) {
        let control_lits: Vec<Lit> = self
            .uts
            .ts
            .latch
            .iter()
            .filter(|v| matches!(hint.get(**v), Some(SignalType::Control)))
            .map(|v| self.uts.lit_next(v.lit(), step))
            .collect();

        if control_lits.is_empty() {
            return;
        }

        let act_var = self.uts.new_var();
        self.solver.new_var_to(act_var);
        let act = act_var.lit();

        for cl in &control_lits {
            self.solver.add_clause(&[!act, *cl]);
        }

        info!(
            "BMC hint-guide step {}: {} control constraints, act_var={}",
            step, control_lits.len(), *act_var
        );

        self.guide_acts.push(act);
    }

    /// Solve at depth k, returns true if counterexample found.
    fn solve_step(&mut self, assump: &LitVec, time_limit: Option<u64>) -> Option<bool> {
        if let Some(limit) = time_limit {
            self.solver
                .solve_with_limit(assump, vec![], Duration::from_secs(limit))
        } else {
            Some(self.solver.solve(assump))
        }
    }
}

impl Engine for BMC {
    fn check(&mut self) -> McResult {
        let start = Instant::now();
        for k in (self.cfg.start..=self.cfg.end).step_by(self.step) {
            let mut time_limit = self.cfg.step_time_limit;
            if let Some(limit) = self.cfg.time_limit {
                let time = start.elapsed().as_secs();
                if time >= limit {
                    return McResult::Unknown(k.checked_sub(1));
                }
                let remain = limit - time;
                time_limit = Some(time_limit.map_or(remain, |tl| tl.min(remain)));
            }
            self.uts.unroll_to(k);
            self.load_trans_to(k);

            if self.cfg.hint_guide {
                if let Some(hint) = self.struct_hint.clone() {
                    self.inject_guide_constraints(hint, k);
                }
            }

            let mut assump: LitVec = self.uts.lits_next(&self.uts.ts.bad, k).collect();
            if self.cfg.kissat {
                for b in assump.iter() {
                    self.solver.add_clause(&[*b]);
                }
                assump.clear();
            }

            let found_cex = if self.cfg.hint_guide && !self.guide_acts.is_empty() {
                // First try with guidance assumptions
                let mut guided_assump = assump.clone();
                guided_assump.extend(self.guide_acts.iter().copied());

                match self.solve_step(&guided_assump, time_limit) {
                    Some(true) => true,
                    Some(false) | None => {
                        // Guided UNSAT or timeout — retry without guidance for completeness
                        match self.solve_step(&assump, time_limit) {
                            Some(true) => true,
                            Some(false) => false,
                            None => { continue; }
                        }
                    }
                }
            } else {
                match self.solve_step(&assump, time_limit) {
                    Some(r) => r,
                    None => { continue; }
                }
            };

            if found_cex {
                self.tracer.trace_state(None, crate::McResult::Unsafe(k));
                return McResult::Unsafe(k);
            }
            self.tracer
                .trace_state(None, crate::McResult::Unknown(Some(k)));
            if self.cfg.kissat {
                self.reset_solver();
            }
        }
        info!("bmc reached bound {}, stopping search", self.cfg.end);
        McResult::Unknown(Some(self.cfg.end))
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn witness(&mut self) -> McWitness {
        let mut wit = self.uts.witness(self.solver.as_ref());
        wit = wit.map(|l| self.rst.restore(l));
        for s in wit.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        wit.exact_state(&self.ots, true);
        McWitness::Bl(wit)
    }
}

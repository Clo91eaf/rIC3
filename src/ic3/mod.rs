use crate::{
    BlProof, BlWitness, Engine, EngineCtrl, McProof, McResult, McWitness,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    gipsat::{SolverStatistic, TransysSolver},
    ic3::{block::BlockResult, localabs::LocalAbs, predprop::PredProp},
    impl_config_deref,
    tracer::{Tracer, TracerIf},
    transys::{
        Transys, TransysCtx, TransysIf, certify::Restore, lift::TsLift, unroll::TransysUnroll,
    },
};
use activity::Activity;
use clap::{ArgAction, Args, Parser};
use frame::{Frame, Frames};
use giputils::{grc::Grc, logger::IntervalLogger};
use log::{Level, debug, error, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, LitVvec, Var, VarSymbols, satif::Satif};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use std::time::Instant;
use utils::Statistic;

mod activity;
mod auxv;
mod block;
mod frame;
mod localabs;
mod mic;
mod predprop;
mod proofoblig;
mod propagate;
mod solver;
mod utils;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub struct IC3Config {
    #[command(flatten)]
    pub base: EngineConfigBase,

    #[command(flatten)]
    pub preproc: PreprocConfig,

    /// dynamic generalization
    #[arg(long = "dynamic", default_value_t = false)]
    pub dynamic: bool,

    /// counterexample to generalization
    #[arg(long = "ctg", action = ArgAction::Set, default_value_t = true)]
    pub ctg: bool,

    /// max number of ctg
    #[arg(long = "ctg-max", default_value_t = 3)]
    pub ctg_max: usize,

    /// ctg limit
    #[arg(long = "ctg-limit", default_value_t = 1)]
    pub ctg_limit: usize,

    /// counterexample to propagation
    #[arg(long = "ctp", default_value_t = false)]
    pub ctp: bool,

    /// internal signals (FMCAD'21 https://doi.org/10.34727/2021/isbn.978-3-85448-046-4_14)
    #[arg(long = "inn", default_value_t = false)]
    pub inn: bool,

    /// abstract constrains
    #[arg(long = "abs-cst", default_value_t = false)]
    pub abs_cst: bool,

    /// abstract trans
    #[arg(long = "abs-trans", default_value_t = false)]
    pub abs_trans: bool,

    /// disable StructHint VSIDS activity boost
    #[arg(long = "no-boost", default_value_t = false)]
    pub no_boost: bool,

    /// disable StructHint MIC domain extension
    #[arg(long = "no-domain", default_value_t = true)]
    pub no_domain: bool,

    /// StructHint MIC: drop datapath literals first during clause generalization
    #[arg(long = "hint-mic", default_value_t = false)]
    pub hint_mic: bool,

    /// StructHint LocalAbs: refine control variables first
    #[arg(long = "hint-refine", default_value_t = false)]
    pub hint_refine: bool,

    /// StructHint alpha: VSIDS activity boost factor (default: from STRUCTHINT_ALPHA env or 2.0)
    #[arg(long = "alpha")]
    pub alpha: Option<f64>,

    /// StructHint push: prioritize pushing clauses with high-score variables
    #[arg(long = "hint-push", default_value_t = false)]
    pub hint_push: bool,

    /// Re-apply hint activity every N conflicts (0=disabled)
    #[arg(long = "hint-reboost", default_value_t = 0)]
    pub hint_reboost: usize,

    /// Cold restart: fully reset VSIDS to SCOAP values every N conflicts (0=disabled)
    #[arg(long = "hint-cold-restart", default_value_t = 0)]
    pub hint_cold_restart: usize,

    /// SCOAP-based domain restriction: only decide variables with score > threshold (0=disabled)
    #[arg(long = "hint-domain")]
    pub hint_domain: Option<f64>,

    /// Adaptive domain: include top N% of scored variables (e.g. 30 = top 30%)
    #[arg(long = "hint-domain-pct")]
    pub hint_domain_pct: Option<u32>,

    /// Slower decay for hinted vars: multiply decay factor by this (e.g. 0.5 = half decay speed)
    #[arg(long = "hint-decay")]
    pub hint_decay: Option<f64>,

    /// Use SCOAP scores as tiebreaker within VSIDS buckets
    #[arg(long = "hint-tiebreak", default_value_t = false)]
    pub hint_tiebreak: bool,

    /// Use VMTF queue initialized with SCOAP scores for variable decisions
    #[arg(long = "hint-vmtf", default_value_t = false)]
    pub hint_vmtf: bool,

    /// Enable curriculum alpha: start high, decay per frame (default: off)
    #[arg(long = "hint-curriculum", default_value_t = false)]
    pub hint_curriculum: bool,

    /// Speculative batch assignment: assign top-K scored variables at once (0=disabled)
    #[arg(long = "hint-speculate", default_value_t = 0)]
    pub hint_speculate: usize,

    /// dropping proof-obligation
    #[arg(
        long = "drop-po", action = ArgAction::Set, default_value_t = true,
    )]
    pub drop_po: bool,

    /// full assignment of last bad (internal parameter)
    #[arg(skip)]
    pub full_bad: bool,

    /// abstract array
    #[arg(long = "abs-array", default_value_t = false)]
    pub abs_array: bool,

    /// finding parent lemma in mic (CAV'23 https://doi.org/10.1007/978-3-031-37703-7_14)
    #[arg(long = "parent-lemma", action = ArgAction::Set, default_value_t = true)]
    pub parent_lemma: bool,

    /// predicate property
    #[arg(long = "pred-prop", default_value_t = false)]
    pub pred_prop: bool,

    /// Local proof (internal parameter)
    #[arg(skip)]
    pub local_proof: bool,
}

impl_config_deref!(IC3Config);

impl Default for IC3Config {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "ic3"]);
        cfg.into_ic3().unwrap()
    }
}

impl IC3Config {
    fn validate(&self) {
        if self.dynamic && self.drop_po {
            error!("cannot enable both dynamic and drop-po");
            panic!();
        }
        if self.inn {
            let pre = "cannot enable both inn and";
            if self.abs_cst || self.abs_trans {
                error!("{pre} (abs_cst or abs_trans)");
                panic!();
            }
        }
        if self.full_bad {
            error!("full-bad can't be used now");
            panic!();
        }
        if self.local_proof {
            if !self.pred_prop {
                error!("local-proof should used with pred-prop");
                panic!();
            }
            if self.prop.is_none() {
                error!("A property ID must be specified for local proof.");
                panic!();
            }
        }
    }
}

pub struct IC3 {
    cfg: IC3Config,
    ts: Transys,
    #[allow(unused)]
    symbols: VarSymbols,
    tsctx: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    inf_solver: TransysSolver,
    lift: TsLift,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    localabs: LocalAbs,
    ots: Transys,
    rst: Restore,
    auxiliary_var: Vec<Var>,
    predprop: Option<PredProp>,

    rng: StdRng,
    filog: IntervalLogger,
    tracer: Tracer,
    ctrl: EngineCtrl,
    struct_hint: Option<crate::structhint::StructHint>,
    adaptive_alpha: f64,
    adaptive_alpha_initial: f64,
    adaptive_last_progress_level: usize,
    adaptive_stall_threshold: usize,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        let nl = self.solvers.len();
        debug!("extending IC3 to level {nl}");
        if let Some(predprop) = self.predprop.as_mut() {
            predprop.extend(self.frame.inf.iter().map(|l| l.as_litvec()));
        }
        // Adaptive alpha: decay when IC3 stalls (no convergence for several frames)
        let levels_since_progress = nl.saturating_sub(self.adaptive_last_progress_level);
        if levels_since_progress > self.adaptive_stall_threshold && self.adaptive_alpha > 1.05 {
            let old_alpha = self.adaptive_alpha;
            // Halve the distance to 1.0
            self.adaptive_alpha = 1.0 + (self.adaptive_alpha - 1.0) * 0.5;
            info!("Adaptive alpha: decayed from {:.3} to {:.3} (stalled for {} levels)",
                  old_alpha, self.adaptive_alpha, levels_since_progress);
        }
        let mut solver = self.inf_solver.clone();
        if let Some(ref hint) = self.struct_hint {
            if !self.cfg.no_boost {
                let frame_alpha = if self.cfg.hint_curriculum {
                    // Curriculum: decay alpha by 0.9^frame, floor at 2.0
                    let decay = 0.9f64.powi(self.level() as i32);
                    let fa = (self.adaptive_alpha * decay).max(2.0);
                    info!("Curriculum alpha: frame={} decay={:.3} alpha={:.3}", self.level(), decay, fa);
                    fa
                } else {
                    self.adaptive_alpha
                };
                solver.dcs.apply_struct_hints(
                    hint, frame_alpha,
                    self.cfg.hint_reboost,
                    self.cfg.hint_cold_restart,
                    self.cfg.hint_decay.unwrap_or(1.0),
                    self.cfg.hint_tiebreak,
                    self.cfg.hint_vmtf,
                    self.cfg.hint_speculate,
                );
            }
        }
        self.solvers.push(solver);
        self.frame.push(Frame::new());
        // Log per-frame boost decision ratio from the previous frame's solver
        if self.solvers.len() >= 2 {
            let prev = &self.solvers[self.solvers.len() - 2];
            if prev.dcs.total_decisions > 0 {
                let ratio = prev.dcs.boost_decisions as f64 / prev.dcs.total_decisions as f64 * 100.0;
                info!("boost_frame[{}]: decisions={}, boosted={}, ratio={:.1}%",
                      self.solvers.len() - 2, prev.dcs.total_decisions, prev.dcs.boost_decisions, ratio);
            }
        }
        if self.level() == 0 {
            for init in self.tsctx.init.clone() {
                self.add_lemma(0, !init, true, None);
            }
            let mut init = LitVec::new();
            for l in self.tsctx.latch.iter() {
                if self.tsctx.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Lit::constant(i.polarity()));
                self.tsctx.add_init(i.var(), Lit::constant(i.polarity()));
            }
        }
    }
}

impl IC3 {
    pub fn new(mut cfg: IC3Config, mut ts: Transys, symbols: VarSymbols, struct_hint: Option<crate::structhint::StructHint>) -> Self {
        cfg.validate();
        let ots = ts.clone();
        if let Some(prop) = cfg.prop {
            if !cfg.local_proof {
                ts.bad = LitVec::from(ts.bad[prop]);
            }
        } else {
            ts.compress_bads();
        }
        let rst = Restore::new(&ts);
        let rng = StdRng::seed_from_u64(cfg.rseed);
        let statistic = Statistic::default();
        let (mut ts, mut rst) = ts.preproc(&cfg.preproc, rst);
        ts.remove_gate_init(&mut rst);
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.inn {
            ts = uts.internal_signals();
        }
        let predprop = cfg.pred_prop.then(|| {
            PredProp::new(
                uts.clone(),
                cfg.local_proof.then(|| cfg.prop.unwrap()),
                cfg.inn,
            )
        });
        let tsctx = Grc::new(ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let initial_alpha: f64 = cfg.alpha.unwrap_or_else(|| {
            std::env::var("STRUCTHINT_ALPHA")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(10.0)
        });
        let adaptive_enabled = std::env::var("STRUCTHINT_ADAPTIVE")
            .ok()
            .and_then(|s| s.parse::<bool>().ok())
            .unwrap_or(false);
        let stall_threshold: usize = std::env::var("STRUCTHINT_STALL_THRESHOLD")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(5);
        // Remap hint variable IDs through preprocessing's forward map
        let struct_hint = struct_hint.map(|hint| {
            hint.remap(|v| rst.try_forward(logicrs::Lit::new(v, false)).map(|l| l.var()))
        });
        // Compute adaptive domain threshold from percentile
        if let Some(pct) = cfg.hint_domain_pct {
            if let Some(ref hint) = struct_hint {
                let mut scores: Vec<f64> = (0..*tsctx.max_var() as usize + 1)
                    .map(|idx| {
                        let var = logicrs::Var::new(idx);
                        let w = hint.activity_weight(var, initial_alpha);
                        (w - 1.0) / (initial_alpha - 1.0).max(0.001)
                    })
                    .filter(|&s| s > 0.01)
                    .collect();
                scores.sort_by(|a, b| b.partial_cmp(a).unwrap());
                if !scores.is_empty() {
                    let idx = (scores.len() as u32 * pct / 100).min(scores.len() as u32 - 1) as usize;
                    let threshold = scores[idx];
                    log::info!("hint-domain-pct {}: threshold={:.3} ({} of {} scored vars in domain)",
                              pct, threshold, idx, scores.len());
                    cfg.hint_domain = Some(threshold);
                }
            }
        }
        let mut inf_solver = TransysSolver::new(&tsctx);
        if let Some(ref hint) = struct_hint {
            if !cfg.no_boost {
                inf_solver.dcs.apply_struct_hints(
                    hint, initial_alpha,
                    cfg.hint_reboost,
                    cfg.hint_cold_restart,
                    cfg.hint_decay.unwrap_or(1.0),
                    cfg.hint_tiebreak,
                    cfg.hint_vmtf,
                    cfg.hint_speculate,
                );
            }
        }
        let lift = TsLift::new(TransysUnroll::new(&ts));
        let mut localabs = LocalAbs::new(&ts, &cfg);
        if (cfg.abs_cst || cfg.abs_trans) {
            if let Some(ref hint) = struct_hint {
                localabs.add_control_vars(hint);
            }
        }
        Self {
            cfg,
            ts,
            symbols,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            localabs,
            auxiliary_var: Vec::new(),
            ots,
            rst,
            predprop,
            rng,
            filog: Default::default(),
            tracer: Tracer::new(),
            ctrl: EngineCtrl::default(),
            struct_hint,
            adaptive_alpha: initial_alpha,
            adaptive_alpha_initial: initial_alpha,
            adaptive_last_progress_level: 0,
            adaptive_stall_threshold: if adaptive_enabled { stall_threshold } else { usize::MAX },
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.inner_invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst.restore_var(l)))
            .collect()
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> McResult {
        if !self.prep_prop_base() {
            self.tracer.trace_state(None, McResult::Unsafe(0));
            return McResult::Unsafe(0);
        }
        self.extend();
        loop {
            let start = Instant::now();
            debug!("blocking phase begin");
            loop {
                match self.block(None) {
                    BlockResult::Failure(depth) => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.tracer.trace_state(None, McResult::Unsafe(depth));
                        return McResult::Unsafe(depth);
                    }
                    BlockResult::Proved => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.tracer.trace_state(None, McResult::Safe);
                        return McResult::Safe;
                    }
                    BlockResult::OverallTimeLimitExceeded => {
                        self.statistic.block.overall_time += start.elapsed();
                        return McResult::Unknown(Some(self.level()));
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    debug!("bad state found in frame {}", self.level());
                    trace!("bad = {bad}");
                    let bad = LitOrdVec::new(bad);
                    let depth = inputs.len() - 1;
                    self.add_obligation(ProofObligation::new(
                        self.level(),
                        bad,
                        inputs,
                        depth,
                        None,
                    ))
                } else {
                    break;
                }
            }
            debug!("blocking phase end");
            self.statistic.block.overall_time += start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.tracer
                .trace_state(None, McResult::Unknown(Some(self.level())));
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            // Track progress for adaptive alpha: propagation moving lemmas = progress
            if propagate || self.frame.early > self.adaptive_last_progress_level {
                self.adaptive_last_progress_level = self.level();
            }
            if propagate {
                self.tracer.trace_state(None, McResult::Safe);
                return McResult::Safe;
            }
            self.propagate_to_inf();
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn proof(&mut self) -> McProof {
        let mut proof = self.ots.clone();
        if let Some(iv) = self.rst.init_var() {
            let piv = proof.add_init_var();
            self.rst.add_restore(iv, piv);
        }
        let mut invariants = self.inner_invariant();
        for c in self.ts.constraint.clone() {
            proof
                .rel
                .migrate(&self.ts.rel, c.var(), &mut self.rst.bvmap);
            invariants.push(LitVec::from(!c));
        }
        let mut invariants: LitVvec = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.rst.restore(*l))))
            .collect();
        invariants.extend(self.rst.eq_invariant());
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let bad = proof.rel.new_or(proof.bad);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, bad]));
        McProof::Bl(BlProof { proof })
    }

    fn witness(&mut self) -> McWitness {
        let mut res = if let Some(res) = self.localabs.witness() {
            res
        } else {
            let mut res = BlWitness::default();
            let b = self.obligations.peak().unwrap();
            assert!(b.frame == 0);
            let mut b = Some(b);
            while let Some(bad) = b {
                res.state.push(bad.state.as_litvec().clone());
                res.input.push(bad.input[0].clone());
                for i in &bad.input[1..] {
                    res.input.push(i.clone());
                    res.state.push(LitVec::new());
                }
                b = bad.next.clone();
            }
            res
        };
        let iv = self.rst.init_var();
        res = res.filter_map(|l| {
            (iv != Some(l.var()))
                .then(|| self.rst.try_restore(l))
                .flatten()
        });
        for s in res.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        res.exact_state(&self.ots, true);
        McWitness::Bl(res)
    }

    fn statistic(&mut self) {
        self.statistic.num_auxiliary_var = self.auxiliary_var.len();
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut statistic = SolverStatistic::default();
        let mut total_decisions: u64 = 0;
        let mut boost_decisions: u64 = 0;
        for s in self.solvers.iter() {
            statistic += *s.statistic();
            total_decisions += s.dcs.total_decisions;
            boost_decisions += s.dcs.boost_decisions;
        }
        // Also count inf_solver
        total_decisions += self.inf_solver.dcs.total_decisions;
        boost_decisions += self.inf_solver.dcs.boost_decisions;
        info!("{statistic:#?}");
        info!("{:#?}", self.statistic);
        if total_decisions > 0 {
            let ratio = boost_decisions as f64 / total_decisions as f64 * 100.0;
            info!("boost_tracking: total_decisions={}, boost_decisions={}, boost_ratio={:.1}%",
                  total_decisions, boost_decisions, ratio);
        }
    }

    fn get_ctrl(&self) -> crate::EngineCtrl {
        self.ctrl.clone()
    }
}

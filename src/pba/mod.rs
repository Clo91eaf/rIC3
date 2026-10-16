//! Optional, activation-core flop abstraction before the ordinary IC3 pipeline.
//!
//! Bounded UNSAT is used only to choose an abstraction. Only IC3 can establish
//! unbounded safety; abstract counterexamples are replayed with every concrete
//! transition enabled, and lifted invariants are checked before reporting SAFE.

use crate::{
    BlEngine, Engine, McResult,
    ic3::{IC3, IC3Config},
    tracer::{Tracer, TracerIf, state_channel_tracer},
    transys::{
        Transys, TransysIf,
        certify::{BlCex, BlProof},
        unroll::TransysUnroll,
    },
    ui::UiRenderer,
    utils::EngineCtrl,
};
use cadical::CaDiCaL;
use clap::Args;
use giputils::{TerminateCtrl, hash::GHashSet};
use log::{info, warn};
use logicrs::{Lit, LitVec, LitVvec, Var, VarSymbols, satif::Satif};
use serde::{Deserialize, Serialize};
use std::{
    sync::{Arc, mpsc},
    thread,
    time::{Duration, Instant},
};

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct PbaConfig {
    /// Enable proof-based flop abstraction before IC3 preprocessing
    #[arg(long = "pba", default_value_t = false)]
    pub enabled: bool,

    /// Maximum bounded-proof depth used to seed the abstraction
    #[arg(long = "pba-depth", default_value_t = 18, value_parser = clap::value_parser!(u32).range(0..=128))]
    pub depth: u32,

    /// Budget for bounded proof/core extraction, in seconds (0 skips PBA)
    #[arg(id = "pba_time_limit", long = "pba-time-limit", default_value_t = 30)]
    pub time_limit: u64,

    /// Maximum spurious-counterexample refinements before concrete fallback
    #[arg(long = "pba-refine-limit", default_value_t = 8)]
    pub refine_limit: usize,
}

impl Default for PbaConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            depth: 18,
            time_limit: 30,
            refine_limit: 8,
        }
    }
}

#[derive(Clone)]
struct Budget {
    deadline: Option<Instant>,
    ctrl: Arc<EngineCtrl>,
}

impl Budget {
    fn stopped(&self) -> bool {
        self.ctrl.is_terminated() || self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    fn capped(&self, seconds: u64) -> Self {
        let deadline = Instant::now().checked_add(Duration::from_secs(seconds));
        Self {
            deadline: match (self.deadline, deadline) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
            ctrl: self.ctrl.clone(),
        }
    }

    // CaDiCaL's handle must not outlive its solver. Join the query before
    // returning, including when cancellation races with solver completion.
    fn solve(&self, solver: &mut CaDiCaL, assumptions: &[Lit], goal: Vec<LitVec>) -> Option<bool> {
        if self.stopped() {
            return None;
        }
        let stop = solver.get_terminate_ctrl();
        thread::scope(|scope| {
            let (tx, rx) = mpsc::channel();
            let join = scope.spawn(move || {
                let result = solver.try_solve(assumptions, goal);
                let _ = tx.send(result);
            });
            let result = loop {
                match rx.recv_timeout(Duration::from_millis(20)) {
                    Ok(result) => break result,
                    Err(mpsc::RecvTimeoutError::Timeout) if !self.stopped() => (),
                    Err(_) => {
                        stop.terminate();
                        break None;
                    }
                }
            };
            join.join().unwrap();
            result
        })
    }
}

// Bound CNF growth before allocating another frame. These limits select a
// smaller abstraction/fallback; they never change the verification result.
const MAX_UNROLL_VARS: usize = 2_000_000;
const MAX_UNROLL_CLAUSES: usize = 8_000_000;

fn within_unroll_limit(ts: &Transys, depth: usize) -> bool {
    (usize::from(ts.max_var()) + ts.latch.len() + 1).saturating_mul(depth.saturating_add(1))
        <= MAX_UNROLL_VARS
        && (ts.trans().count() + ts.constraint.len() + 2 * ts.latch.len())
            .saturating_mul(depth.saturating_add(1))
            <= MAX_UNROLL_CLAUSES
}

/// Optional connections are grouped by next-state variable (including shared
/// and complemented next expressions). An activation enables its entire group
/// at every frame, exactly as required for a time-independent abstraction.
fn core_latches(ts: &Transys, unroll: &TransysUnroll<Transys>, solver: &CaDiCaL) -> GHashSet<Var> {
    ts.latch
        .iter()
        .copied()
        .filter(|q| solver.unsat_has(unroll.opt[&ts.next[q].var()].lit()))
        .collect()
}

fn seed_abstraction(ts: &Transys, cfg: &PbaConfig, seed: u64, budget: &Budget) -> GHashSet<Var> {
    let concrete = || ts.latch.iter().copied().collect();
    if budget.stopped() || !within_unroll_limit(ts, 0) {
        return concrete();
    }
    let mut unroll = TransysUnroll::new(ts);
    unroll.enable_optional_connect();
    let mut solver = CaDiCaL::new();
    solver.set_seed(seed);
    solver.reserve(unroll.max_var);
    ts.load_init(&mut solver);
    unroll.load_trans(&mut solver, 0, true);
    let mut assumptions: Vec<_> = unroll.opt.values().map(|v| v.lit()).collect();
    assumptions.sort_unstable();
    let mut keep = GHashSet::new();
    let mut proved = false;
    // Query 0, 1, 2, 4, 8, ... and the requested final depth. Accumulate cores
    // so the seed preserves every bounded proof obtained in this phase.
    let mut bounds = vec![0];
    let mut depth = 1;
    while depth < cfg.depth as usize {
        bounds.push(depth);
        depth *= 2;
    }
    if cfg.depth > 0 {
        bounds.push(cfg.depth as usize);
    }
    for bound in bounds {
        if budget.stopped() || !within_unroll_limit(ts, bound) {
            break;
        }
        while unroll.num_unroll < bound {
            unroll.unroll();
            solver.reserve(unroll.max_var);
            unroll.load_trans(&mut solver, unroll.num_unroll, true);
            if budget.stopped() {
                break;
            }
        }
        if budget.stopped() {
            break;
        }
        let goal = unroll.lits_next(&ts.bad, bound).collect();
        match budget.solve(&mut solver, &assumptions, vec![goal]) {
            Some(false) => {
                proved = true;
                keep.extend(core_latches(ts, &unroll, &solver));
                info!(
                    "PBA bound {bound}: UNSAT, retaining {}/{} latches",
                    keep.len(),
                    ts.latch.len()
                );
            }
            Some(true) => {
                info!("PBA bound {bound}: concrete counterexample exists; ending core extraction");
                break;
            }
            None => {
                info!("PBA core extraction interrupted or budget exhausted");
                break;
            }
        }
    }
    if proved { keep } else { concrete() }
}

/// Preserve variable identities for proof lifting and replay. Removed state
/// becomes a fresh choice each cycle. Initial equalities in the abstract cone
/// (also relational initializers) remain mandatory only on the first cycle;
/// unknown init stays unknown. All environment constraints are retained.
fn abstract_model(ts: &Transys, keep: &GHashSet<Var>) -> Transys {
    let mut abs = ts.clone();
    let mut initial = Vec::new();
    for &q in &ts.latch {
        if !keep.contains(&q) {
            abs.input.push(q);
            abs.next.remove(&q);
            if let Some(init) = abs.init.remove(&q) {
                initial.push((q, init));
            }
        }
    }
    abs.latch.retain(|q| keep.contains(q));
    // Do not keep otherwise dead cut state alive just to constrain its first
    // input value. Follow initial expressions too: a retained state may have
    // a relational initializer that depends on a cut state's initial value.
    let mut needed = GHashSet::new();
    let mut queue: Vec<_> = abs
        .bad
        .iter()
        .chain(abs.constraint.iter())
        .chain(abs.justice.iter())
        .map(|l| l.var())
        .collect();
    while let Some(v) = queue.pop() {
        if !needed.insert(v) {
            continue;
        }
        if let Some(n) = abs.next.get(&v) {
            queue.push(n.var());
        }
        if let Some(i) = ts.init.get(&v) {
            queue.push(i.var());
        }
        queue.extend(abs.rel.dep(v).iter().copied());
    }
    initial.retain(|(q, _)| needed.contains(q));
    if !initial.is_empty() {
        let start = abs.add_init_var().lit();
        for (q, init) in initial {
            let equal = abs.rel.new_xnor(q.lit(), init);
            let guard = abs.rel.new_imply(start, equal);
            abs.constraint.push(guard);
        }
    }
    abs
}

enum Replay {
    Real(BlCex),
    Spurious(GHashSet<Var>),
    Unavailable,
}

fn replay(ts: &Transys, trace: &BlCex, budget: &Budget) -> Replay {
    let Some(depth) = trace.len().checked_sub(1) else {
        return Replay::Unavailable;
    };
    bounded_query(ts, depth, Some(trace), budget)
}

fn bounded_query(ts: &Transys, depth: usize, trace: Option<&BlCex>, budget: &Budget) -> Replay {
    if budget.stopped() || !within_unroll_limit(ts, depth) {
        return Replay::Unavailable;
    }
    let mut unroll = TransysUnroll::new(ts);
    unroll.enable_optional_connect();
    let mut solver = CaDiCaL::new();
    solver.reserve(unroll.max_var);
    ts.load_init(&mut solver);
    let inputs: GHashSet<_> = ts.input.iter().copied().collect();
    for k in 0..=depth {
        if k > 0 {
            unroll.unroll();
        }
        solver.reserve(unroll.max_var);
        unroll.load_trans(&mut solver, k, true);
        // Cut-state values are internal abstraction choices, not primary
        // inputs to the concrete circuit. Recompute them existentially to
        // avoid refining irrelevant state just to reproduce arbitrary noise.
        if let Some(trace) = trace {
            for &lit in trace.input[k]
                .iter()
                .filter(|l| inputs.contains(&l.var()))
                .chain(trace.state[k].iter().filter(|l| ts.is_latch(l.var())))
            {
                solver.add_clause(&[unroll.lit_next(lit, k)]);
            }
        }
        if budget.stopped() {
            return Replay::Unavailable;
        }
    }
    let mut assumptions: Vec<_> = unroll.opt.values().map(|v| v.lit()).collect();
    assumptions.sort_unstable();
    let goal = unroll.lits_next(&ts.bad, depth).collect();
    match budget.solve(&mut solver, &assumptions, vec![goal]) {
        Some(true) => {
            let mut cex = unroll.cex(&solver);
            cex.bad_id = ts
                .bad
                .iter()
                .position(|&b| solver.sat_value(unroll.lit_next(b, depth)) == Some(true))
                .unwrap();
            Replay::Real(cex)
        }
        Some(false) => Replay::Spurious(core_latches(ts, &unroll, &solver)),
        None => Replay::Unavailable,
    }
}

fn lift_proof(ts: &Transys, mut proof: BlProof) -> BlProof {
    // merge() only appends roots with fresh variables. Force an alias even if
    // the worker's entire invariant simplified to an existing literal.
    let bads = proof.bad.clone();
    let bad = proof.rel.new_or(bads);
    let root = proof.new_var();
    proof
        .rel
        .add_rel(root, &LitVvec::cnf_assign(root.lit(), bad));
    proof.bad = LitVec::from(root.lit());
    // Abstract constraints must be proved, never imported as assumptions on
    // the concrete model. IC3's certificate includes their violations in bad.
    proof.constraint.clear();
    let mut result = ts.clone();
    result.merge(&proof, |v| (v <= ts.max_var()).then_some(v));
    result.compress_bads();
    BlProof::new(result)
}

/// Independent SAT checks of initiation and consecution on the lifted concrete
/// transition system. Original bad is explicitly included by lift_proof().
fn validate_proof(proof: &BlProof, budget: &Budget) -> Option<bool> {
    let mut solver = CaDiCaL::new();
    solver.reserve(proof.max_var());
    proof.load_init(&mut solver);
    proof.load_trans(&mut solver, true);
    match budget.solve(&mut solver, &[], vec![proof.bad.clone()]) {
        Some(false) => (),
        Some(true) => return Some(false),
        None => return None,
    }
    let mut unroll = TransysUnroll::new(&proof.proof);
    unroll.unroll();
    let mut solver = CaDiCaL::new();
    solver.reserve(unroll.max_var);
    unroll.load_trans(&mut solver, 0, true);
    unroll.load_trans(&mut solver, 1, true);
    let assumptions: Vec<_> = proof.bad.iter().map(|&b| !b).collect();
    let next_bad = unroll.lits_next(&proof.bad, 1).collect();
    budget
        .solve(&mut solver, &assumptions, vec![next_bad])
        .map(|sat| !sat)
}

pub struct PbaEngine {
    cfg: IC3Config,
    ts: Transys,
    symbols: VarSymbols,
    ctrl: Arc<EngineCtrl>,
    tracer: Tracer,
    renderer: Option<UiRenderer>,
    inner: Option<IC3>,
    proof: Option<BlProof>,
    cex: Option<BlCex>,
    completed_depth: Option<usize>,
}

impl PbaEngine {
    pub fn new(cfg: IC3Config, mut ts: Transys, symbols: VarSymbols) -> Self {
        cfg.validate();
        assert!(!cfg.local_proof, "PBA does not support IC3 local proofs");
        assert!(cfg.pba.depth <= 128, "PBA depth must be at most 128");
        if let Some(prop) = cfg.prop {
            ts.bad = LitVec::from(ts.bad[prop]);
        }
        Self {
            cfg,
            ts,
            symbols,
            ctrl: Arc::new(EngineCtrl::new()),
            tracer: Tracer::new(),
            renderer: None,
            inner: None,
            proof: None,
            cex: None,
            completed_depth: None,
        }
    }

    fn run_inner(&mut self, model: Transys, budget: &Budget) -> McResult {
        self.inner = None;
        let mut cfg = self.cfg.clone();
        cfg.pba.enabled = false;
        cfg.prop = None; // Already selected, before core extraction.
        cfg.time_limit = budget.deadline.map(|d| {
            d.saturating_duration_since(Instant::now())
                .as_secs()
                .saturating_add(1)
        });
        if let Some(limit) = cfg.time_limit {
            cfg.preproc.scorr_tl = cfg.preproc.scorr_tl.min(limit);
            cfg.preproc.frts_tl = cfg.preproc.frts_tl.min(limit);
        }
        let mut inner = IC3::new(cfg, model, self.symbols.clone());
        inner.set_ctrl(self.ctrl.clone());
        if let Some(renderer) = self.renderer.clone() {
            inner.set_ui(renderer);
        }
        let (tx, rx) = state_channel_tracer();
        inner.add_tracer(Box::new(tx));
        // Terminal abstract results cannot escape to portfolio/state tracers
        // until their counterexample or certificate has passed validation.
        let result = thread::scope(|scope| {
            let join = scope.spawn(|| inner.check());
            while !join.is_finished() {
                if let Ok((_, result)) = rx.recv_timeout(Duration::from_millis(20)) {
                    self.progress(result);
                }
                if budget.stopped() {
                    self.ctrl.terminate();
                }
            }
            for (_, result) in rx.try_iter() {
                self.progress(result);
            }
            join.join().unwrap()
        });
        self.inner = Some(inner);
        result
    }

    fn progress(&mut self, result: McResult) {
        if let McResult::Unknown(Some(depth)) = result
            && self.completed_depth.is_none_or(|old| depth > old)
        {
            self.completed_depth = Some(depth);
            self.tracer.trace_state(None, result);
        }
    }

    fn check_with_budget(&mut self, budget: &Budget) -> McResult {
        let start = Instant::now();
        let mut keep = seed_abstraction(
            &self.ts,
            &self.cfg.pba,
            self.cfg.rseed,
            &budget.capped(self.cfg.pba.time_limit),
        );
        info!(
            "PBA seed: {}/{} retained latches, {:.3}s",
            keep.len(),
            self.ts.latch.len(),
            start.elapsed().as_secs_f64()
        );
        let mut refinements = 0;
        loop {
            if budget.stopped() {
                return McResult::Unknown(self.completed_depth);
            }
            let concrete = keep.len() == self.ts.latch.len();
            let model = abstract_model(&self.ts, &keep);
            info!(
                "PBA checking {} model: {}",
                if concrete { "concrete" } else { "abstract" },
                model.statistic()
            );
            match self.run_inner(model, budget) {
                McResult::UNSAT => {
                    let proof = self.inner.as_mut().unwrap().proof();
                    if concrete {
                        self.proof = Some(proof);
                        return McResult::UNSAT;
                    }
                    let proof = lift_proof(&self.ts, proof);
                    match validate_proof(&proof, budget) {
                        Some(true) => {
                            info!(
                                "PBA lifted invariant passed concrete initiation and consecution checks"
                            );
                            self.proof = Some(proof);
                            return McResult::UNSAT;
                        }
                        Some(false) => {
                            warn!("PBA certificate validation failed; falling back to concrete IC3")
                        }
                        None => return McResult::Unknown(self.completed_depth),
                    }
                }
                McResult::SAT(depth) => {
                    let trace = self.inner.as_mut().unwrap().cex();
                    if concrete {
                        let mut trace = trace;
                        trace.bad_id = self.cfg.prop.unwrap_or(trace.bad_id);
                        self.cex = Some(trace);
                        return McResult::SAT(depth);
                    }
                    match replay(&self.ts, &trace, budget) {
                        Replay::Real(mut trace) => {
                            trace.bad_id = self.cfg.prop.unwrap_or(trace.bad_id);
                            let depth = trace.len() - 1;
                            info!(
                                "PBA counterexample replayed on the concrete model at depth {depth}"
                            );
                            self.cex = Some(trace);
                            return McResult::SAT(depth);
                        }
                        Replay::Spurious(core) if refinements < self.cfg.pba.refine_limit => {
                            let before = keep.len();
                            keep.extend(core);
                            // A trace core excludes one witness, and may add
                            // only one bit of a wide state. A property-wide
                            // bounded core can eliminate all abstract bad
                            // traces at this depth in one refinement. If the
                            // query times out, the trace core remains valid.
                            match bounded_query(
                                &self.ts,
                                depth,
                                None,
                                &budget.capped(self.cfg.pba.time_limit),
                            ) {
                                Replay::Spurious(core) => {
                                    info!(
                                        "PBA property core at depth {depth}: {} latches",
                                        core.len()
                                    );
                                    keep.extend(core);
                                }
                                Replay::Real(mut trace) => {
                                    trace.bad_id = self.cfg.prop.unwrap_or(trace.bad_id);
                                    let depth = trace.len() - 1;
                                    self.cex = Some(trace);
                                    return McResult::SAT(depth);
                                }
                                Replay::Unavailable => (),
                            }
                            if keep.len() > before {
                                refinements += 1;
                                info!(
                                    "PBA refinement {refinements}: spurious depth {depth}, retaining {}/{} latches",
                                    keep.len(),
                                    self.ts.latch.len()
                                );
                                continue;
                            }
                            warn!("PBA replay core added no latches; falling back to concrete IC3");
                        }
                        _ => info!(
                            "PBA replay/refinement limit reached; falling back to concrete IC3"
                        ),
                    }
                }
                McResult::Unknown(_) => return McResult::Unknown(self.completed_depth),
            }
            keep.extend(self.ts.latch.iter().copied());
        }
    }
}

impl Engine for PbaEngine {
    fn check(&mut self) -> McResult {
        let budget = Budget {
            deadline: self
                .cfg
                .time_limit
                .and_then(|t| Instant::now().checked_add(Duration::from_secs(t))),
            ctrl: self.ctrl.clone(),
        };
        let result = self.check_with_budget(&budget);
        if !matches!(result, McResult::Unknown(_)) {
            self.tracer.trace_state(None, result);
        }
        result
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn set_ui(&mut self, renderer: UiRenderer) {
        self.renderer = Some(renderer);
    }

    fn get_ctrl(&self) -> Arc<dyn TerminateCtrl> {
        self.ctrl.clone()
    }

    fn statistic(&mut self) {
        if let Some(inner) = self.inner.as_mut() {
            inner.statistic();
        }
    }
}

impl BlEngine for PbaEngine {
    fn proof(&mut self) -> BlProof {
        self.proof
            .as_ref()
            .expect("PBA proof requires a SAFE result")
            .clone()
    }

    fn cex(&mut self) -> BlCex {
        self.cex
            .as_ref()
            .expect("PBA counterexample requires a SAT result")
            .clone()
    }
}

#[cfg(test)]
mod tests;

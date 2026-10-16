//! Proof-node gate/state abstraction following observed JG PBA construction.
//!
//! Bounded UNSAT is used only to choose an abstraction. Only IC3 can establish
//! unbounded safety; abstract counterexamples are replayed with every concrete
//! transition enabled, and lifted invariants are checked before reporting SAFE.

#[cfg(test)]
mod captured;
mod encoding;
mod live;
mod model;
mod prepare;
mod proof;

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
    /// Enable proof-based gate/state abstraction before IC3 preprocessing
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

    /// Export each proof selection, concrete projection and abstract model
    #[arg(long = "pba-dump-dir", value_name = "DIR")]
    pub dump: Option<std::path::PathBuf>,
}

impl Default for PbaConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            depth: 18,
            time_limit: 30,
            refine_limit: 8,
            dump: None,
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

enum Replay {
    Real(BlCex),
    Spurious,
    Unavailable(&'static str),
}

fn replay(ts: &Transys, trace: &BlCex, budget: &Budget) -> Replay {
    let Some(depth) = trace.len().checked_sub(1) else {
        return Replay::Unavailable("empty abstract trace");
    };
    let inputs: GHashSet<_> = ts.input.iter().copied().collect();
    let mut e = live::Encoding::new(ts, CaDiCaL::new());
    e.initial();
    let mut goal = LitVec::new();
    for k in 0..=depth {
        if budget.stopped() {
            return Replay::Unavailable("concrete replay time limit");
        }
        e.constraints(k);
        goal = e.goal(k);
        // Only retained state and true primary inputs constrain replay.
        // Cut gate/state inputs are existentially completed on the concrete TS.
        for &lit in trace.input[k]
            .iter()
            .filter(|l| inputs.contains(&l.var()))
            .chain(trace.state[k].iter().filter(|l| ts.is_latch(l.var())))
        {
            let mapped = e.reference(lit, k);
            e.clause(&[mapped]);
        }
        if !e.resources_ok() {
            return Replay::Unavailable("concrete replay unroll limit");
        }
        if k < depth {
            e.transition(k);
        }
    }
    match budget.solve(&mut e.solver, &[], vec![goal]) {
        Some(true) => {
            let concrete = e.trace(depth);
            match validate_trace(ts, &concrete, budget) {
                Some(true) => Replay::Real(concrete),
                Some(false) => Replay::Unavailable("counterexample rejected by original CNF"),
                None => Replay::Unavailable("counterexample validation time limit"),
            }
        }
        Some(false) => Replay::Spurious,
        None => Replay::Unavailable("concrete replay SAT time limit"),
    }
}

// Check the completed witness with the original, unflattened CNF. Complete
// state vectors let us check one step at a time, without another deep unroll.
fn validate_trace(ts: &Transys, trace: &BlCex, budget: &Budget) -> Option<bool> {
    let last = trace.len().checked_sub(1)?;
    if trace.bad_id >= ts.bad.len() {
        return Some(false);
    }
    for k in 0..=last {
        let mut solver = CaDiCaL::new();
        solver.reserve(ts.max_var());
        ts.load_trans(&mut solver, true);
        if k == 0 {
            ts.load_init(&mut solver);
        }
        for &lit in trace.input[k].iter().chain(trace.state[k].iter()) {
            solver.add_clause(&[lit]);
        }
        if k < last {
            for &next in &trace.state[k + 1] {
                solver.add_clause(&[ts.next[&next.var()].not_if(!next.polarity())]);
            }
        } else {
            solver.add_clause(&[ts.bad[trace.bad_id]]);
        }
        match budget.solve(&mut solver, &[], vec![])? {
            true => (),
            false => return Some(false),
        }
    }
    Some(true)
}

fn lift_proof(
    ts: &Transys,
    mut proof: BlProof,
    projection: &giputils::hash::GHashMap<Var, Var>,
) -> BlProof {
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
    result.merge(&proof, |v| {
        projection
            .get(&v)
            .copied()
            .or_else(|| (v <= ts.max_var()).then_some(v))
    });
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

    fn accept_counterexample(&mut self, mut trace: BlCex) -> McResult {
        trace.bad_id = self.cfg.prop.unwrap_or(trace.bad_id);
        let depth = trace.len() - 1;
        self.cex = Some(trace);
        McResult::SAT(depth)
    }

    fn check_with_budget(&mut self, budget: &Budget) -> McResult {
        use prepare::Prepared;
        let mut generation = 0;
        let mut abstraction = match prepare::prepare(
            &self.ts,
            &self.cfg.pba,
            self.cfg.rseed,
            &budget.capped(self.cfg.pba.time_limit),
            0,
            &mut generation,
        ) {
            Prepared::Model(model) => Some(model),
            Prepared::Counterexample(trace) => return self.accept_counterexample(trace),
            Prepared::Unavailable(reason) => {
                info!("PBA preparation unavailable ({reason}); checking concrete model");
                None
            }
        };
        let mut refinements = 0;
        loop {
            if budget.stopped() {
                return McResult::Unknown(self.completed_depth);
            }
            let model = abstraction
                .as_ref()
                .map_or_else(|| self.ts.clone(), |a| a.ts.clone());
            info!(
                "PBA checking {} model: {}",
                if abstraction.is_some() {
                    "abstract"
                } else {
                    "concrete"
                },
                model.statistic()
            );
            match self.run_inner(model, budget) {
                McResult::UNSAT => {
                    let mut proof = self.inner.as_mut().unwrap().proof();
                    if let Some(abs) = &abstraction {
                        proof = lift_proof(&self.ts, proof, &abs.projection);
                        match validate_proof(&proof, budget) {
                            Some(true) => info!(
                                "PBA lifted invariant passed concrete initiation and consecution checks"
                            ),
                            Some(false) => {
                                warn!("PBA lifted proof rejected; checking concrete model");
                                abstraction = None;
                                continue;
                            }
                            None => return McResult::Unknown(self.completed_depth),
                        }
                    }
                    self.proof = Some(proof);
                    return McResult::UNSAT;
                }
                McResult::SAT(depth) => {
                    let trace = self.inner.as_mut().unwrap().cex();
                    let Some(abs) = &abstraction else {
                        return self.accept_counterexample(trace);
                    };
                    info!("PBA replaying abstract counterexample at depth {depth}");
                    let projected = trace.filter_map_var(|v| {
                        abs.projection
                            .get(&v)
                            .copied()
                            .or_else(|| (v <= self.ts.max_var()).then_some(v))
                    });
                    match replay(&self.ts, &projected, budget) {
                        Replay::Real(trace) => return self.accept_counterexample(trace),
                        Replay::Spurious if refinements < self.cfg.pba.refine_limit => {
                            info!(
                                "PBA concrete replay rejected the trace; selecting a fresh prefix proof"
                            );
                            match prepare::prepare(
                                &self.ts,
                                &self.cfg.pba,
                                self.cfg.rseed,
                                &budget.capped(self.cfg.pba.time_limit),
                                depth,
                                &mut generation,
                            ) {
                                Prepared::Model(next) => {
                                    if next.selected == abs.selected {
                                        warn!(
                                            "PBA selection unchanged after spurious depth {depth}; checking concrete model"
                                        );
                                        abstraction = None;
                                    } else {
                                        refinements += 1;
                                        info!(
                                            "PBA refinement {refinements}: replaced selection after spurious depth {depth}"
                                        );
                                        abstraction = Some(next);
                                    }
                                }
                                Prepared::Counterexample(trace) => {
                                    return self.accept_counterexample(trace);
                                }
                                Prepared::Unavailable(reason) => {
                                    info!(
                                        "PBA refinement at depth {depth} unavailable ({reason}); checking concrete model"
                                    );
                                    abstraction = None;
                                }
                            }
                        }
                        Replay::Spurious => {
                            info!(
                                "PBA refinement limit {} reached at depth {depth}; checking concrete model",
                                self.cfg.pba.refine_limit
                            );
                            abstraction = None;
                        }
                        Replay::Unavailable(reason) => {
                            info!(
                                "PBA concrete replay unavailable at depth {depth} ({reason}); checking concrete model"
                            );
                            abstraction = None;
                        }
                    }
                }
                McResult::Unknown(_) => return McResult::Unknown(self.completed_depth),
            }
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

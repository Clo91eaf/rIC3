use super::{Budget, Replay, live::Encoding, proof::Dependencies, replay};
use crate::transys::{Transys, certify::BlCex};
use cadical::CaDiCaL;
use giputils::hash::GHashSet;
use log::info;
use logicrs::{Var, satif::Satif};

pub(super) enum ProofResult {
    Unsat(GHashSet<Var>),
    Sat(BlCex),
    Unavailable(&'static str),
}

/// JG 0x8b47d0 encodes targets at EVERY context first, constraints and
/// transitions backwards, and initial values last. Each proof is fresh.
pub(super) fn prove(ts: &Transys, depth: usize, seed: u64, budget: &Budget) -> ProofResult {
    if budget.stopped() {
        return ProofResult::Unavailable("PBA time limit or termination");
    }
    let dependencies = Box::pin(Dependencies::default());
    let mut solver = CaDiCaL::new();
    solver.set_seed(seed);
    solver.connect_tracer(dependencies.as_ref());
    let mut e = Encoding::new(ts, solver);
    if !e.prefix(depth) {
        e.solver.disconnect_tracer(dependencies.as_ref());
        return ProofResult::Unavailable("PBA proof unroll size limit");
    }
    let answer = budget.solve(&mut e.solver, &[], vec![]);
    e.solver.disconnect_tracer(dependencies.as_ref());
    match answer {
        Some(true) => {
            // Independently complete/check the demand encoder's witness using
            // the original full transition encoding before reporting a CEX.
            match replay(ts, &e.trace(depth), budget) {
                Replay::Real(trace) => ProofResult::Sat(trace),
                _ => ProofResult::Unavailable("bounded counterexample validation failed"),
            }
        }
        Some(false) => {
            let mut core = match dependencies.core() {
                Ok(core) => core,
                Err(reason) => return ProofResult::Unavailable(reason),
            };
            let original_size = core.clauses.len();
            drop(dependencies);
            // Reprove the core while independently checking it. CaDiCaL's
            // first proof can contain avoidable dependencies; a fresh proof
            // of only its original premises removes those dependencies.
            // The resulting abstraction is independently prefix-checked too.
            for pass in 0..4 {
                let reduced_dependencies = Box::pin(Dependencies::default());
                let mut checker = CaDiCaL::new();
                checker.connect_tracer(reduced_dependencies.as_ref());
                checker.reserve(Var::new(e.origins.len() - 1));
                for c in &core.clauses {
                    checker.add_clause(c);
                }
                let checked = budget.solve(&mut checker, &[], vec![]);
                checker.disconnect_tracer(reduced_dependencies.as_ref());
                match checked {
                    Some(false) => (),
                    Some(true) => {
                        return ProofResult::Unavailable("extracted proof core is satisfiable");
                    }
                    None if pass == 0 => {
                        return ProofResult::Unavailable("proof core validation time limit");
                    }
                    None => break,
                }
                let Ok(reduced) = reduced_dependencies.core() else {
                    break;
                };
                let stable = reduced.clauses.len() == core.clauses.len();
                info!(
                    "PBA core reproof {} at depth {depth}: {} -> {} original clauses",
                    pass + 1,
                    core.clauses.len(),
                    reduced.clauses.len()
                );
                core = reduced;
                if stable {
                    break;
                }
            }
            let selected: GHashSet<_> = core
                .variables
                .iter()
                .filter_map(|v| e.origins[usize::from(*v)])
                .collect();
            info!(
                "PBA proof depth {depth}: {} proof nodes, {} / {original_size} original clauses after core reproof, {} SAT variables, {} model seeds ({} encoded SAT variables)",
                core.proof_nodes,
                core.clauses.len(),
                core.variables.len(),
                selected.len(),
                e.origins.len()
            );
            ProofResult::Unsat(selected)
        }
        None => ProofResult::Unavailable("PBA SAT proof time limit"),
    }
}

pub(super) enum Probe {
    Leak(usize),
    NoLeak,
    Unavailable(&'static str),
}

pub(super) fn check_prefix(ts: &Transys, depth: usize, budget: &Budget) -> Option<bool> {
    let mut compact = ts.clone();
    let mut restore = crate::transys::certify::Restore::new(&compact);
    compact.rearrange(&mut restore);
    let ts = &compact;
    if budget.stopped() {
        return None;
    }
    let mut e = Encoding::new(ts, CaDiCaL::new());
    if !e.prefix(depth) {
        return None;
    }
    budget.solve(&mut e.solver, &[], vec![])
}

/// JG 0x8cc510: check the first bad frame incrementally with a shared
/// 10000-conflict budget. An inconclusive probe hands the model to IC3.
pub(super) fn scout(ts: &Transys, first: usize, last: usize, budget: &Budget) -> Probe {
    let mut compact = ts.clone();
    let mut restore = crate::transys::certify::Restore::new(&compact);
    compact.rearrange(&mut restore);
    let ts = &compact;
    let mut solver = CaDiCaL::new();
    solver.enable_conflict_counter();
    let mut e = Encoding::new(ts, solver);
    e.initial();
    for k in 0..=last {
        if budget.stopped() {
            return Probe::Unavailable("PBA leak probe budget exhausted");
        }
        e.constraints(k);
        let goal = e.goal(k);
        if !e.resources_ok() {
            return Probe::Unavailable("PBA leak probe unroll limit");
        }
        if k >= first {
            let used = e.solver.conflicts();
            if used >= 10_000 {
                return Probe::Unavailable("shared 10000-conflict leak probe budget exhausted");
            }
            e.solver.limit_conflicts((10_000 - used) as i32);
            let answer = budget.solve(&mut e.solver, &[], vec![goal.clone()]);
            info!(
                "PBA leak probe depth {k}: {answer:?}, {} / 10000 conflicts",
                e.solver.conflicts()
            );
            match answer {
                Some(true) => return Probe::Leak(k),
                Some(false) => (),
                None => return Probe::Unavailable("PBA leak probe conflict/time budget exhausted"),
            }
        }
        for b in goal {
            e.clause(&[!b]);
        }
        if k < last {
            e.transition(k);
        }
    }
    Probe::NoLeak
}

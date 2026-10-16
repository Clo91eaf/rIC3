use super::{
    Budget, PbaConfig,
    encoding::{self, Probe, ProofResult},
    model::{self, Abstraction},
};
use crate::transys::{Transys, TransysIf, certify::BlCex};
use log::{info, warn};

pub(super) enum Prepared {
    Model(Box<Abstraction>),
    Counterexample(BlCex),
    Unavailable(&'static str),
}

impl Prepared {
    fn model(model: Abstraction) -> Self {
        Self::Model(Box::new(model))
    }
}

pub(super) fn prepare(
    ts: &Transys,
    cfg: &PbaConfig,
    seed: u64,
    budget: &Budget,
    initial: usize,
    generation: &mut usize,
) -> Prepared {
    let mut depth = initial;
    let limit = (cfg.depth as usize).max(initial).min(128);
    let mut previous: Option<Abstraction> = None;
    loop {
        match encoding::prove(ts, depth, seed, budget) {
            ProofResult::Sat(trace) => return Prepared::Counterexample(trace),
            ProofResult::Unavailable(reason) => {
                info!("PBA preparation stopped at depth {depth}: {reason}");
                return previous.map_or(Prepared::Unavailable(reason), Prepared::model);
            }
            ProofResult::Unsat(seed) => {
                let selected = model::complete_selection(ts, &seed);
                let dropped = previous
                    .as_ref()
                    .map_or(0, |p| p.selected.difference(&selected).count());
                let abstract_model = model::build(ts, selected);
                match encoding::check_prefix(&abstract_model.ts, depth, budget) {
                    Some(false) => (),
                    Some(true) => {
                        warn!("PBA proof selection failed its abstract prefix check at {depth}");
                        return previous.map_or(
                            Prepared::Unavailable("abstract prefix validation failed"),
                            Prepared::model,
                        );
                    }
                    None => {
                        return previous.map_or(
                            Prepared::Unavailable("abstract prefix check budget exhausted"),
                            Prepared::model,
                        );
                    }
                }
                info!(
                    "PBA model depth {depth}: {} retained source latches, {} cut inputs ({} gate cuts), {dropped} old selections removed; {}",
                    ts.latch
                        .iter()
                        .filter(|v| abstract_model.selected.contains(v))
                        .count(),
                    abstract_model.cuts,
                    abstract_model.cut_gates,
                    abstract_model.ts.statistic()
                );
                if let Some(dir) = &cfg.dump {
                    let export = (|| -> std::io::Result<()> {
                        std::fs::create_dir_all(dir)?;
                        let stem = format!("round-{}-depth-{depth}", *generation);
                        std::fs::write(
                            dir.join(format!("{stem}.model.json")),
                            serde_json::to_vec(&abstract_model.ts)?,
                        )?;
                        let mut selected: Vec<_> =
                            abstract_model.selected.iter().copied().collect();
                        selected.sort_unstable();
                        let mut seeds: Vec<_> = seed.iter().copied().collect();
                        seeds.sort_unstable();
                        let mut projection: Vec<_> = abstract_model
                            .projection
                            .iter()
                            .map(|(a, b)| (*a, *b))
                            .collect();
                        projection.sort_unstable();
                        std::fs::write(
                            dir.join(format!("{stem}.selection.json")),
                            serde_json::to_vec(
                                &serde_json::json!({"depth":depth,"seeds":seeds,"selected":selected,
                                "projection":projection,"cuts":abstract_model.cuts,"gate_cuts":abstract_model.cut_gates,
                                "removed_previous_selections":dropped}),
                            )?,
                        )?;
                        Ok(())
                    })();
                    if let Err(error) = export {
                        warn!("PBA dump failed: {error}");
                    }
                }
                *generation += 1;
                // The observed p530 policy probes the next ten frames before
                // entering N. An inconclusive probe also hands off to IC3.
                // The wall-clock cap supplements the shared SAT conflict cap.
                let first = depth + 1;
                let last = (depth + 10).min(128);
                let probe = if first <= last {
                    encoding::scout(&abstract_model.ts, first, last, budget)
                } else {
                    Probe::NoLeak
                };
                match probe {
                    Probe::Leak(next) if next <= limit => {
                        info!(
                            "PBA bounded leak at {next}; recomputing proof selection from the concrete source"
                        );
                        previous = Some(abstract_model);
                        depth = next;
                    }
                    Probe::Leak(next) => {
                        info!(
                            "PBA bounded leak at {next} exceeds preparation depth {limit}; handing model to IC3"
                        );
                        return Prepared::model(abstract_model);
                    }
                    Probe::NoLeak => {
                        info!("PBA no bounded leak in {first}..={last}; handing model to IC3");
                        return Prepared::model(abstract_model);
                    }
                    Probe::Unavailable(reason) => {
                        info!(
                            "PBA bounded leak probe inconclusive ({reason}); handing model to IC3"
                        );
                        return Prepared::model(abstract_model);
                    }
                }
            }
        }
    }
}

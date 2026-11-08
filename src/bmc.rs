use crate::{
    BlCex, BlEngine, Engine, McResult,
    config::{EngineConfig, EngineConfigBase, PreprocConfig},
    impl_config_deref,
    tracer::{ExtractorIf, Tracer, TracerIf},
    transys::{Transys, certify::Restore, nodep::NoDepTransys},
};
use clap::{Args, Parser};
use giputils::TerminateCtrl;
use logicrs::LitVec;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

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
}

impl_config_deref!(BMCConfig);

impl Default for BMCConfig {
    fn default() -> Self {
        let cfg = EngineConfig::parse_from(["", "bmc"]);
        cfg.into_bmc().unwrap()
    }
}

/// BMC with rBMC (deps/rBMC) on the preprocessed model.
pub struct BMC {
    bmc: rbmc::Bmc,
    rst: Restore,
    tracer: Tracer,
    extractor: Option<Box<dyn ExtractorIf>>,
}

impl BMC {
    pub fn new(cfg: BMCConfig, mut ts: Transys) -> Self {
        ts.compress_bads();
        let rst = Restore::new(&ts);
        let (ts, rst) = ts.preproc(&cfg.preproc, rst);
        let mut ts = ts.remove_dep();
        ts.assert_constraint();
        let bmc_cfg = rbmc::Config {
            start: cfg.start,
            end: cfg.end,
            step: cfg.step as usize,
            dyn_step: cfg.dyn_step,
            time_limit: cfg.time_limit,
            step_time_limit: cfg.step_time_limit,
            kissat: cfg.kissat,
            seed: cfg.rseed,
        };
        Self {
            bmc: rbmc::Bmc::new(bmc_cfg, to_model(ts)),
            rst,
            tracer: Tracer::new(),
            extractor: None,
        }
    }
}

/// The rBMC model of a preprocessed transition system, with the same
/// variables.
fn to_model(ts: NoDepTransys) -> rbmc::Model {
    assert!(ts.bad.len() == 1, "bmc expects one bad literal");
    assert!(ts.constraint.is_empty());
    rbmc::Model {
        input: ts.input,
        latch: ts.latch,
        next: ts.next,
        init: ts.init,
        bad: ts.bad[0],
        constraint: LitVec::new(),
        rel: ts.rel,
    }
}

/// Passes the progress to the tracer and the invariants of the extractor
/// (lemmas that hold in all frames) to rBMC.
struct Hooks<'a> {
    tracer: &'a mut Tracer,
    extractor: &'a mut Option<Box<dyn ExtractorIf>>,
}

impl rbmc::Hooks for Hooks<'_> {
    fn bound_checked(&mut self, k: usize, sat: bool) {
        let r = if sat {
            McResult::SAT(k)
        } else {
            McResult::Unknown(Some(k))
        };
        self.tracer.trace_state(None, r);
    }

    fn invariants(&mut self) -> Vec<LitVec> {
        let mut invs = Vec::new();
        if let Some(extractor) = self.extractor.as_mut() {
            while let Some((k, lemma)) = extractor.extract_lemma() {
                if k.is_none() {
                    invs.push(lemma);
                }
            }
        }
        invs
    }
}

impl Engine for BMC {
    fn check(&mut self) -> McResult {
        let mut hooks = Hooks {
            tracer: &mut self.tracer,
            extractor: &mut self.extractor,
        };
        match self.bmc.check(&mut hooks) {
            rbmc::BmcResult::Sat(k) => McResult::SAT(k),
            rbmc::BmcResult::Unknown(k) => McResult::Unknown(k),
        }
    }

    fn add_tracer(&mut self, tracer: Box<dyn TracerIf>) {
        self.tracer.add_tracer(tracer);
    }

    fn set_extractor(&mut self, extractor: Box<dyn ExtractorIf>) {
        self.extractor = Some(extractor);
    }

    fn get_ctrl(&self) -> Arc<dyn TerminateCtrl> {
        self.bmc.ctrl()
    }
}

impl BlEngine for BMC {
    fn cex(&mut self) -> BlCex {
        let c = self.bmc.cex();
        let mut cex = BlCex {
            input: c.input,
            state: c.state,
            ..Default::default()
        };
        cex = cex.map(|l| self.rst.restore(l));
        for s in cex.state.iter_mut() {
            *s = self.rst.restore_eq_state(s);
        }
        cex
    }
}

use giputils::hash::GHashMap;
use logicrs::{Lit, Var};

/// Per-drop success predictor: fixed-coefficient logistic regression trained
/// offline on 6.8M drop attempts from 76 solved HWMCC'20 cases (engine-feature
/// AUC 0.892, causal time split). Used to (a) order the cube most-droppable
/// first and (b) skip attempts predicted below a probability threshold
/// (skipped literals are simply kept — sound, the lemma just stays larger).
///
/// The per-var history (attempts/successes so far in this run) is the online
/// component; everything else is static per attempt.
pub struct DropPredictor {
    hist: GHashMap<Var, (u32, u32)>,
    pub threshold: f64,
}

const LR_BIAS: f64 = -4.277005;
const LR_W_ACT: f64 = -1.320510;
const LR_W_LEN: f64 = 1.226044e-2;
const LR_W_FRAME: f64 = -3.136560e-2;
const LR_W_LEVEL: f64 = 2.664598e-2;
const LR_W_FRAME_FRAC: f64 = 2.218253;
const LR_W_INPAR: f64 = -2.601279;
const LR_W_POL: f64 = -1.503356e-1;
const LR_W_HIST_RATE: f64 = 4.661986;
const LR_W_HIST_ATT: f64 = 1.661935e-1;
/// smoothing prior for the per-var history rate (pooled base success rate)
const GLOBAL_RATE: f64 = 0.19;

impl DropPredictor {
    pub fn new(threshold: f64) -> Self {
        Self {
            hist: GHashMap::new(),
            threshold,
        }
    }

    pub fn predict(
        &self,
        lit: Lit,
        act: f64,
        len: usize,
        frame: usize,
        level: usize,
        inpar: bool,
    ) -> f64 {
        let (att, suc) = self.hist.get(&lit.var()).copied().unwrap_or((0, 0));
        let hist_rate = (suc as f64 + 5.0 * GLOBAL_RATE) / (att as f64 + 5.0);
        let hist_att = (1.0 + att as f64).ln();
        let frame_frac = frame as f64 / level.max(1) as f64;
        let z = LR_BIAS
            + LR_W_ACT * act
            + LR_W_LEN * len as f64
            + LR_W_FRAME * frame as f64
            + LR_W_LEVEL * level as f64
            + LR_W_FRAME_FRAC * frame_frac
            + LR_W_INPAR * (inpar as u8) as f64
            + LR_W_POL * (lit.polarity() as u8) as f64
            + LR_W_HIST_RATE * hist_rate
            + LR_W_HIST_ATT * hist_att;
        1.0 / (1.0 + (-z).exp())
    }

    pub fn record(&mut self, var: Var, success: bool) {
        let e = self.hist.entry(var).or_insert((0, 0));
        e.0 += 1;
        if success {
            e.1 += 1;
        }
    }
}

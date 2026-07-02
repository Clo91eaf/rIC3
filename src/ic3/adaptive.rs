use std::time::{Duration, Instant};

/// Online controller deciding how much MIC minimization is worth doing.
///
/// Two arms:
/// - arm 0 (aggressive): stop the drop loop after 1 consecutive failed drop (fail limit = 1)
/// - arm 1 (thorough): minimize to fixpoint (fail limit = 0, the classic MIC)
///
/// Reward is frame-depth progress per wall-clock second. Time is divided into
/// windows; at each window boundary the active arm is credited with the depth
/// gained during the window, then the next arm is chosen greedily by
/// depth/time rate, with periodic re-exploration of the lesser-played arm.
/// Stats decay exponentially so the controller can track phase changes within
/// a single run. Any stopping point is sound: a non-minimal lemma is still a
/// valid relatively-inductive clause.
pub struct MicAdaptive {
    window: Duration,
    arms: [ArmStat; 2],
    active: usize,
    window_start: Instant,
    depth_at_window_start: usize,
    windows: usize,
    /// windows played per arm (for logging)
    pub played: [usize; 2],
}

#[derive(Default, Clone, Copy)]
struct ArmStat {
    /// decayed seconds spent with this arm active
    time: f64,
    /// decayed frame-depth advanced while this arm was active
    depth: f64,
}

impl ArmStat {
    fn rate(&self) -> f64 {
        if self.time < 1e-3 {
            // optimistic: an unplayed arm gets tried first
            f64::INFINITY
        } else {
            self.depth / self.time
        }
    }
}

/// re-explore the lesser-played arm every this many windows
const EXPLORE_EVERY: usize = 8;
/// per-window exponential decay of arm stats (~30-window memory)
const DECAY: f64 = 0.97;

impl MicAdaptive {
    pub fn new(window: Duration) -> Self {
        Self {
            window,
            arms: [ArmStat::default(); 2],
            active: 0,
            window_start: Instant::now(),
            depth_at_window_start: 0,
            windows: 0,
            played: [0; 2],
        }
    }

    /// Called at each mic; returns the fail limit to use (0 = minimize to fixpoint).
    pub fn decide(&mut self, depth: usize) -> usize {
        let now = Instant::now();
        let elapsed = now - self.window_start;
        if elapsed >= self.window {
            for arm in self.arms.iter_mut() {
                arm.time *= DECAY;
                arm.depth *= DECAY;
            }
            let arm = &mut self.arms[self.active];
            arm.time += elapsed.as_secs_f64();
            arm.depth += depth.saturating_sub(self.depth_at_window_start) as f64;
            self.windows += 1;
            self.window_start = now;
            self.depth_at_window_start = depth;
            self.active = if self.windows % EXPLORE_EVERY == 0 {
                // re-explore whichever arm has less (decayed) playtime
                if self.arms[0].time <= self.arms[1].time { 0 } else { 1 }
            } else if self.arms[0].rate() >= self.arms[1].rate() {
                0
            } else {
                1
            };
            self.played[self.active] += 1;
        }
        if self.active == 0 { 1 } else { 0 }
    }
}

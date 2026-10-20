use super::*;
use crate::{
    bmc::{BMC, BMCConfig},
    tracer::{StateTracerIf, state_channel_tracer},
};

/// Two-bit counter from zero; bad when equal to `bad`.
fn counter(bad: usize) -> Transys {
    let mut ts = Transys::new();
    let lo = ts.new_var();
    let hi = ts.new_var();
    let next_hi = ts.rel.new_xor(lo.lit(), hi.lit());
    ts.add_latch(lo, Some(Lit::FALSE), !lo.lit());
    ts.add_latch(hi, Some(Lit::FALSE), next_hi);
    let is_bad = ts.rel.new_and([
        lo.lit().not_if((bad & 1) == 0),
        hi.lit().not_if((bad & 2) == 0),
    ]);
    ts.bad.push(is_bad);
    ts
}

/// Latch stuck at zero, bad when set; the property is inductive.
fn stuck_latch() -> Transys {
    let mut ts = Transys::new();
    let latch = ts.new_var();
    ts.add_latch(latch, Some(Lit::FALSE), latch.lit());
    ts.bad.push(latch.lit());
    ts
}

fn ic3(end: usize, pred_prop: bool, ts: Transys) -> IC3 {
    let mut cfg = IC3Config::default();
    cfg.end = end;
    cfg.pred_prop = pred_prop;
    IC3::new(cfg, ts, VarSymbols::default())
}

/// Runs the engine and returns its result and the traced state events.
fn run(mut engine: impl Engine) -> (McResult, Vec<McResult>) {
    let (tx, rx) = state_channel_tracer();
    engine.add_tracer(Box::new(tx));
    let result = engine.check();
    let events = rx.try_iter().map(|(_, result)| result).collect();
    (result, events)
}

#[test]
fn results_and_traces_match_bmc() {
    for (bad, end) in [(0, 0), (3, 0), (3, 2), (3, 3), (3, usize::MAX)] {
        let mut cfg = BMCConfig::default();
        cfg.end = end;
        let expected = run(BMC::new(cfg, counter(bad)));
        for pred_prop in [false, true] {
            assert_eq!(
                run(ic3(end, pred_prop, counter(bad))),
                expected,
                "bad={bad}, end={end}, pred_prop={pred_prop}"
            );
        }
    }
}

struct TerminateAtDepth(Arc<dyn TerminateCtrl>, usize);

impl TracerIf for TerminateAtDepth {}

#[intertrait::cast_to]
impl StateTracerIf for TerminateAtDepth {
    fn trace_state(&mut self, _: Option<usize>, result: McResult) {
        if result == McResult::Unknown(Some(self.1)) {
            self.0.terminate();
        }
    }
}

#[test]
fn termination_reports_the_last_completed_depth() {
    for pred_prop in [false, true] {
        let mut engine = ic3(usize::MAX, pred_prop, counter(3));
        engine.add_tracer(Box::new(TerminateAtDepth(engine.get_ctrl(), 1)));
        let (result, events) = run(engine);
        assert_eq!(result, McResult::Unknown(Some(1)), "pred_prop={pred_prop}");
        assert_eq!(
            events,
            vec![McResult::Unknown(Some(0)), McResult::Unknown(Some(1))]
        );
    }
}

#[test]
fn bound_does_not_prevent_a_proof() {
    for end in [10, usize::MAX] {
        let (result, events) = run(ic3(end, false, stuck_latch()));
        assert_eq!(result, McResult::UNSAT);
        assert_eq!(events.iter().filter(|&&r| r == McResult::UNSAT).count(), 1);
    }
}

/// 3-bit counter 0..=5 that wraps to 0; bad when it reaches `bad`.
fn mod6_counter(bad: usize) -> Transys {
    let mut ts = Transys::new();
    let b: Vec<Var> = (0..3).map(|_| ts.new_var()).collect();
    let l: Vec<Lit> = b.iter().map(|v| v.lit()).collect();
    // value == 5 (101) wraps to 0.
    let at5 = ts.rel.new_and([l[0], !l[1], l[2]]);
    let c1 = l[0];
    let c2 = ts.rel.new_and([l[0], l[1]]);
    let n0 = !l[0];
    let n1 = ts.rel.new_xor(l[1], c1);
    let n2 = ts.rel.new_xor(l[2], c2);
    let n: Vec<Lit> = [n0, n1, n2]
        .into_iter()
        .map(|x| ts.rel.new_and([x, !at5]))
        .collect();
    for i in 0..3 {
        ts.add_latch(b[i], Some(Lit::FALSE), n[i]);
    }
    let is_bad = ts
        .rel
        .new_and((0..3).map(|i| l[i].not_if((bad >> i) & 1 == 0)));
    ts.bad.push(is_bad);
    ts
}

fn reach_ic3(ts: Transys, exact: bool, sim: usize) -> IC3 {
    let mut cfg = IC3Config::default();
    cfg.reach_mic = true;
    cfg.reach_push = true;
    cfg.may_po = true;
    cfg.may_po_share = 1.0;
    cfg.may_po_min_shrink = 1;
    cfg.reach_mic_exact = exact;
    cfg.reach_sim = sim;
    IC3::new(cfg, ts, VarSymbols::default())
}

#[test]
fn reach_cache_flags_parse() {
    let cfg = EngineConfig::parse_from(["", "ic3", "--reach-cache"])
        .into_ic3()
        .unwrap();
    assert!(cfg.reach_mic && cfg.reach_push && cfg.may_po);
    let cfg = EngineConfig::parse_from(["", "ic3", "--reach-cache", "--reach-mic", "false"])
        .into_ic3()
        .unwrap();
    assert!(!cfg.reach_mic && cfg.reach_push && cfg.may_po);
    let cfg = IC3Config::default();
    assert!(!cfg.reach_enabled());
}

#[test]
fn reach_cache_results_match_bmc() {
    for bad in 0..8 {
        for (exact, sim) in [(false, 0), (true, 0), (false, 64)] {
            let mut bcfg = BMCConfig::default();
            bcfg.end = 10;
            let expected = run(BMC::new(bcfg, mod6_counter(bad))).0;
            let got = run(reach_ic3(mod6_counter(bad), exact, sim)).0;
            match expected {
                McResult::SAT(d) => assert_eq!(got, McResult::SAT(d), "bad={bad}"),
                _ => assert_eq!(got, McResult::UNSAT, "bad={bad}"),
            }
        }
    }
    for bad in [0, 1, 2, 3] {
        let expected = run(BMC::new(BMCConfig::default(), counter(bad))).0;
        assert_eq!(run(reach_ic3(counter(bad), false, 16)).0, expected);
    }
}

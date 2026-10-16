use super::*;
use crate::{config::EngineConfig, create_bl_engine, tracer::state_channel_tracer};

fn budget() -> Budget {
    Budget {
        deadline: Some(Instant::now() + Duration::from_secs(10)),
        ctrl: Arc::new(EngineCtrl::new()),
    }
}

fn cfg(depth: u32) -> IC3Config {
    let mut cfg = IC3Config::default();
    cfg.pba.enabled = true;
    cfg.pba.depth = depth;
    cfg
}

fn safe_model() -> (Transys, Var, Var) {
    let mut ts = Transys::new();
    let q = ts.new_var();
    let irrelevant = ts.new_var();
    ts.add_latch(q, Some(Lit::FALSE), q.lit());
    ts.add_latch(irrelevant, Some(Lit::FALSE), !irrelevant.lit());
    ts.bad.push(q.lit());
    (ts, q, irrelevant)
}

fn sat_frames(ts: &Transys, frames: &[Vec<Lit>]) -> bool {
    let mut u = TransysUnroll::new(ts);
    u.unroll_to(frames.len() - 1);
    let mut s = CaDiCaL::new();
    s.reserve(u.max_var);
    ts.load_init(&mut s);
    for (k, frame) in frames.iter().enumerate() {
        u.load_trans(&mut s, k, true);
        for &lit in frame {
            s.add_clause(&[u.lit_next(lit, k)]);
        }
    }
    s.solve(&[])
}

fn projected_frames(abs: &model::Abstraction, frames: &[Vec<Lit>]) -> Vec<Vec<Lit>> {
    frames
        .iter()
        .map(|frame| {
            let mut result = Vec::new();
            for &lit in frame {
                if abs.ts.is_latch(lit.var()) || abs.ts.input.contains(&lit.var()) {
                    result.push(lit);
                }
                for (&mapped, &source) in abs.projection.iter() {
                    if source == lit.var() && abs.ts.input.contains(&mapped) {
                        result.push(lit.map_var(|_| mapped));
                    }
                }
            }
            result
        })
        .collect()
}

#[test]
fn abstraction_preserves_initial_values_relations_and_environment() {
    for init in [None, Some(Lit::FALSE), Some(Lit::TRUE)] {
        let mut ts = Transys::new();
        let q = ts.new_var();
        let r = ts.new_var();
        let input = ts.new_var();
        ts.add_input(input);
        ts.add_latch(q, init, !q.lit());
        // A relational initializer also restricts a retained latch through a
        // cut latch. It cannot be replaced with independent constant values.
        ts.add_latch(r, Some(!q.lit()), q.lit());
        let environment = ts.rel.new_imply(r.lit(), input.lit());
        ts.constraint.push(environment);
        ts.bad.push(r.lit());
        for keep in [GHashSet::new(), [r].into_iter().collect()] {
            let abs = model::build(&ts, model::complete_selection(&ts, &keep));
            for bits in 0..8 {
                let frame: Vec<_> = [q, r, input]
                    .into_iter()
                    .enumerate()
                    .map(|(bit, v)| v.lit().not_if(bits & (1 << bit) == 0))
                    .collect();
                assert_eq!(
                    sat_frames(&ts, std::slice::from_ref(&frame)),
                    sat_frames(&abs.ts, &projected_frames(&abs, &[frame]))
                );
            }
            // Exhaustively check two-cycle concrete trace inclusion.
            for bits in 0..64 {
                let frames: Vec<Vec<_>> = (0..2)
                    .map(|k| {
                        [q, r, input]
                            .into_iter()
                            .enumerate()
                            .map(|(bit, v)| v.lit().not_if(bits & (1 << (3 * k + bit)) == 0))
                            .collect()
                    })
                    .collect();
                if sat_frames(&ts, &frames) {
                    assert!(sat_frames(&abs.ts, &projected_frames(&abs, &frames)));
                }
            }
        }
    }
}

#[test]
fn cut_initial_value_is_free_after_the_first_cycle() {
    let (ts, q, _) = safe_model();
    let abs = model::build(&ts, model::complete_selection(&ts, &GHashSet::new()));
    assert!(!sat_frames(
        &abs.ts,
        &projected_frames(&abs, &[vec![q.lit()]])
    ));
    assert!(sat_frames(
        &abs.ts,
        &projected_frames(&abs, &[vec![!q.lit()], vec![q.lit()]])
    ));
    assert!(!sat_frames(&ts, &[vec![!q.lit()], vec![q.lit()]]));
}

#[test]
fn bounded_core_keeps_relevant_state_and_cuts_noise() {
    let (ts, q, noise) = safe_model();
    let encoding::ProofResult::Unsat(seed) = encoding::prove(&ts, 4, 0, &budget()) else {
        panic!()
    };
    let keep = model::complete_selection(&ts, &seed);
    assert!(keep.contains(&q));
    assert!(!keep.contains(&noise));
    let abs = model::build(&ts, keep);
    assert!(
        abs.ts.constraint.is_empty(),
        "dead initial guards must not retain cut noise"
    );
    assert_eq!(abs.ts.latch, vec![q]);
}

#[test]
fn property_core_covers_input_choices_beyond_one_spurious_trace() {
    let mut ts = Transys::new();
    let q = ts.new_var();
    let r = ts.new_var();
    let input = ts.new_var();
    ts.add_input(input);
    ts.add_latch(q, Some(Lit::FALSE), q.lit());
    ts.add_latch(r, Some(Lit::FALSE), r.lit());
    let q_bad = ts.rel.new_and([input.lit(), q.lit()]);
    let r_bad = ts.rel.new_and([!input.lit(), r.lit()]);
    ts.bad.push(ts.rel.new_or([q_bad, r_bad]));
    let trace = BlCex {
        input: vec![LitVec::from(!input.lit()); 2],
        state: vec![LitVec::new(); 2],
        bad_id: 0,
    };
    assert!(matches!(replay(&ts, &trace, &budget()), Replay::Spurious));
    let encoding::ProofResult::Unsat(property_core) = encoding::prove(&ts, 1, 0, &budget()) else {
        panic!()
    };
    assert!(property_core.contains(&q) && property_core.contains(&r));
}

#[test]
fn safe_abstract_proof_is_lifted_and_validated() {
    for preproc in [false, true] {
        let (mut ts, q, noise) = safe_model();
        // Keep the cut state in the abstract cone to exercise a first-cycle
        // guard and certificate extension with an auxiliary pulse latch.
        ts.bad = LitVec::from(ts.rel.new_and([q.lit(), noise.lit()]));
        let mut cfg = cfg(2);
        cfg.preproc.preproc = preproc;
        // Fix the abstraction for this certificate test: a different valid
        // SAT proof may legitimately retain both latches and need no pulse.
        let abs = model::build(
            &ts,
            model::complete_selection(&ts, &[q].into_iter().collect()),
        );
        assert!(abs.ts.latch.iter().any(|q| !ts.latch.contains(q)));
        let mut engine = PbaEngine::new(cfg, ts.clone(), VarSymbols::new());
        assert_eq!(engine.run_inner(abs.ts, &budget()), McResult::UNSAT);
        let proof = lift_proof(&ts, engine.inner.as_mut().unwrap().proof(), &abs.projection);
        assert_eq!(validate_proof(&proof, &budget()), Some(true));
        assert!(ts.latch.iter().all(|q| proof.latch.contains(q)));
        assert!(ts.input.iter().all(|i| proof.input.contains(i)));
        assert_eq!(proof.constraint, ts.constraint);
        assert!(
            proof.latch.len() > ts.latch.len(),
            "must exercise lifting, not concrete fallback"
        );
    }
}

#[test]
fn concrete_proof_checks_reject_bad_initialization_and_noninduction() {
    let (mut ts, q, _) = safe_model();
    ts.init.insert(q, Lit::TRUE);
    assert_eq!(
        validate_proof(&BlProof::new(ts.clone()), &budget()),
        Some(false)
    );
    ts.init.insert(q, Lit::FALSE);
    ts.next.insert(q, !q.lit());
    assert_eq!(validate_proof(&BlProof::new(ts), &budget()), Some(false));
}

#[test]
fn spurious_trace_refines_before_reporting_a_real_counterexample() {
    for refine_limit in [0, 8] {
        let mut ts = Transys::new();
        let q = ts.new_var();
        let r = ts.new_var();
        ts.add_latch(q, Some(Lit::FALSE), Lit::TRUE);
        ts.add_latch(r, Some(Lit::FALSE), q.lit());
        ts.bad.push(r.lit());
        let mut cfg = cfg(0); // Empty seed; abstract bad at 1 is spurious.
        cfg.pba.refine_limit = refine_limit;
        let mut engine = create_bl_engine(EngineConfig::IC3(cfg), ts.clone(), VarSymbols::new());
        let (tx, rx) = state_channel_tracer();
        engine.add_tracer(Box::new(tx));
        assert_eq!(engine.check(), McResult::SAT(2));
        let events: Vec<_> = rx.try_iter().map(|(_, r)| r).collect();
        assert_eq!(
            events
                .iter()
                .filter(|r| matches!(r, McResult::SAT(_)))
                .collect::<Vec<_>>(),
            vec![&McResult::SAT(2)]
        );
        let trace = engine.cex();
        assert_eq!(trace.len(), 3);
        assert!(matches!(replay(&ts, &trace, &budget()), Replay::Real(_)));
    }
}

#[test]
fn zero_budget_and_termination_return_unknown_without_certificate() {
    let (ts, _, _) = safe_model();
    let mut config = cfg(2);
    config.time_limit = Some(0);
    let mut engine = PbaEngine::new(config, ts.clone(), VarSymbols::new());
    assert_eq!(engine.check(), McResult::Unknown(None));
    assert!(engine.proof.is_none() && engine.cex.is_none());
    let mut engine = PbaEngine::new(cfg(2), ts, VarSymbols::new());
    engine.get_ctrl().terminate();
    assert_eq!(engine.check(), McResult::Unknown(None));
    assert!(engine.proof.is_none() && engine.cex.is_none());
}

#[test]
fn initial_counterexample_and_unknown_init_are_not_lost() {
    for init in [None, Some(Lit::TRUE)] {
        let mut ts = Transys::new();
        let q = ts.new_var();
        ts.add_latch(q, init, Lit::FALSE);
        ts.bad.push(q.lit());
        let mut engine = PbaEngine::new(cfg(2), ts, VarSymbols::new());
        assert_eq!(engine.check(), McResult::SAT(0));
        assert_eq!(engine.cex().state[0], LitVec::from(q.lit()));
    }
}

#[test]
fn selected_property_preserves_counterexample_id() {
    let (mut ts, q, _) = safe_model();
    ts.bad.push(!q.lit());
    let mut config = cfg(2);
    config.prop = Some(1);
    let mut engine = PbaEngine::new(config, ts, VarSymbols::new());
    assert_eq!(engine.check(), McResult::SAT(0));
    assert_eq!(engine.cex().bad_id, 1);
}

#[test]
fn bounded_check_cannot_report_unbounded_safety() {
    let mut ts = Transys::new();
    let q = ts.new_var();
    ts.add_latch(q, Some(Lit::FALSE), !q.lit());
    ts.bad.push(q.lit());
    let mut config = cfg(0);
    config.end = 0;
    let mut engine = PbaEngine::new(config, ts, VarSymbols::new());
    assert_eq!(engine.check(), McResult::Unknown(Some(0)));
    assert!(engine.proof.is_none());
}

#[test]
fn small_circuits_match_exhaustive_bmc_with_valid_certificates() {
    use crate::bmc::{BMC, BMCConfig};
    // Three state bits have at most eight reachable states. BMC through depth
    // eight is a complete reachability oracle for these finite circuits.
    for case in 0..32 {
        let mut ts = Transys::new();
        let q = ts.new_var();
        let r = ts.new_var();
        let noise = ts.new_var();
        let input = ts.new_var();
        ts.add_input(input);
        let xor = ts.rel.new_xor(q.lit(), r.lit());
        let choices = [
            Lit::FALSE,
            Lit::TRUE,
            q.lit(),
            !q.lit(),
            r.lit(),
            !r.lit(),
            xor,
            input.lit(),
        ];
        let q_init = [None, Some(Lit::FALSE), Some(Lit::TRUE), Some(!r.lit())][case % 4];
        ts.add_latch(q, q_init, choices[case % choices.len()]);
        ts.add_latch(r, Some(Lit::FALSE), choices[(case / 4 + 2) % choices.len()]);
        ts.add_latch(noise, None, !noise.lit());
        if case % 3 == 0 {
            let c = ts.rel.new_imply(r.lit(), input.lit());
            ts.constraint.push(c);
        }
        ts.bad.push(if case % 2 == 0 { q.lit() } else { xor });
        let bmc_cfg = BMCConfig {
            base: crate::config::EngineConfigBase {
                end: 8,
                ..Default::default()
            },
            ..Default::default()
        };
        let expected = BMC::new(bmc_cfg, ts.clone()).check();
        let mut config = cfg(if case % 2 == 0 { 0 } else { 2 });
        config.time_limit = Some(5);
        config.pred_prop = case % 4 == 0;
        let mut engine = PbaEngine::new(config, ts.clone(), VarSymbols::new());
        let actual = engine.check();
        match expected {
            McResult::SAT(_) => {
                assert!(
                    matches!(actual, McResult::SAT(_)),
                    "case={case}, actual={actual:?}"
                );
                assert!(
                    matches!(replay(&ts, &engine.cex(), &budget()), Replay::Real(_)),
                    "case={case}"
                );
            }
            _ => {
                assert_eq!(actual, McResult::UNSAT, "case={case}");
                assert_eq!(
                    validate_proof(&engine.proof(), &budget()),
                    Some(true),
                    "case={case}"
                );
            }
        }
    }
}

#[test]
fn original_cnf_rejects_invalid_completed_witnesses() {
    let mut ts = Transys::new();
    let q = ts.new_var();
    ts.add_latch(q, Some(Lit::FALSE), Lit::TRUE);
    ts.bad.push(q.lit());
    let trace = |values: &[bool]| BlCex {
        input: vec![LitVec::new(); values.len()],
        state: values
            .iter()
            .map(|&b| LitVec::from(q.lit().not_if(!b)))
            .collect(),
        bad_id: 0,
    };
    assert_eq!(
        validate_trace(&ts, &trace(&[false, true]), &budget()),
        Some(true)
    );
    assert_eq!(
        validate_trace(&ts, &trace(&[true, true]), &budget()),
        Some(false)
    );
    assert_eq!(
        validate_trace(&ts, &trace(&[false, false, true]), &budget()),
        Some(false)
    );
    assert_eq!(
        validate_trace(&ts, &trace(&[false]), &budget()),
        Some(false)
    );
}

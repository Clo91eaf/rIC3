use std::{io::Write, process::Command};

const SAFE: &str = "1 sort bitvec 1
2 zero 1
3 state 1 q
4 state 1 noise
5 init 1 3 2
6 init 1 4 2
7 next 1 3 3
8 not 1 4
9 next 1 4 8
10 and 1 3 4
11 bad 10
";

const UNSAFE: &str = "1 sort bitvec 1
2 zero 1
3 one 1
4 state 1 q
5 state 1 r
6 state 1 s
7 init 1 4 2
8 init 1 5 2
9 init 1 6 2
10 next 1 4 3
11 next 1 5 4
12 next 1 6 5
13 bad 6
";

fn run(model: &str, args: &[&str]) -> String {
    let mut file = tempfile::Builder::new()
        .suffix(".btor2")
        .tempfile()
        .unwrap();
    file.write_all(model.as_bytes()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(file.path())
        .args(["--ui", "false"])
        .args(args)
        .env("RUST_LOG", "info")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

#[test]
fn opt_in_pba_exports_a_safe_certificate() {
    let dir = tempfile::tempdir().unwrap();
    let certificate = dir.path().join("proof.btor2");
    let output = run(
        SAFE,
        &[
            "--cert",
            certificate.to_str().unwrap(),
            "ic3",
            "--pba",
            "--pba-depth",
            "1",
        ],
    );
    assert!(output.contains("PBA model depth"), "{output}");
    assert!(output.contains("lifted invariant passed"), "{output}");
    assert!(output.ends_with("UNSAT\n"), "{output}");
    let model = btor::Btor::from_file(&certificate);
    // Check the serialized certificate as a fresh transition system, without
    // word-level simplification (which could hide non-inductive invariants).
    use rIC3::frontend::{Frontend, btor::BtorFrontend};
    let mut frontend = BtorFrontend::new(model);
    let (wts, _) = frontend.wts();
    let (proof, _) = wts.bitblast_to_ts();
    use logicrs::{LitVec, satif::Satif};
    use rIC3::transys::{TransysIf, unroll::TransysUnroll};
    let mut solver = cadical::CaDiCaL::new();
    proof.load_init(&mut solver);
    proof.load_trans(&mut solver, true);
    assert!(!solver.solve_with_constraint(&[], vec![proof.bad.clone()]));
    let mut unroll = TransysUnroll::new(&proof);
    unroll.unroll();
    let mut solver = cadical::CaDiCaL::new();
    unroll.load_trans(&mut solver, 0, true);
    unroll.load_trans(&mut solver, 1, true);
    let assumptions: Vec<_> = proof.bad.iter().map(|b| !*b).collect();
    let bad: LitVec = unroll.lits_next(&proof.bad, 1).collect();
    assert!(!solver.solve_with_constraint(&assumptions, vec![bad]));
}

#[test]
fn spurious_counterexample_is_not_exported() {
    let output = run(UNSAFE, &["--cex", "ic3", "--pba", "--pba-depth", "0"]);
    assert!(output.contains("PBA refinement 1"), "{output}");
    assert!(output.contains("\nSAT\nsat\nb0\n"), "{output}");
    assert!(output.contains("counterexample at depth 3"), "{output}");
    assert!(
        !output.contains("found a counterexample at depth 2"),
        "{output}"
    );
}

#[test]
fn pba_is_off_by_default_and_respects_zero_overall_budget() {
    let output = run(SAFE, &["ic3"]);
    assert!(!output.contains("PBA"));
    assert!(output.ends_with("UNSAT\n"));
    let output = run(UNSAFE, &["--cex", "ic3", "--pba", "--time-limit", "0"]);
    assert!(output.ends_with("UNKNOWN\n2\n"), "{output}");
}

#[test]
fn deep_aig_pba_falls_back_to_cnf_and_proves_safety() {
    // q starts false and holds its value, so the AND of q and all inputs is
    // unreachable. PBA retains the entire q-to-bad path. Recursive frontend
    // normalization of this legal circuit used to abort with a stack overflow.
    const GATES: usize = 12_000;
    let q = 2 * (GATES + 1);
    let mut model = format!("aag {} {GATES} 1 0 {GATES} 1\n", 2 * GATES + 1);
    for input in 1..=GATES {
        model.push_str(&format!("{}\n", 2 * input));
    }
    model.push_str(&format!("{q} {q} 0\n{}\n", 2 * (2 * GATES + 1)));
    let mut previous = q;
    for input in 1..=GATES {
        let gate = 2 * (GATES + 1 + input);
        model.push_str(&format!("{gate} {previous} {}\n", 2 * input));
        previous = gate;
    }
    let mut file = tempfile::Builder::new().suffix(".aag").tempfile().unwrap();
    file.write_all(model.as_bytes()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ric3"))
        .arg("check")
        .arg(file.path())
        .args([
            "--ui",
            "false",
            "ic3",
            "--pba",
            "--preproc",
            "false",
            "--time-limit",
            "10",
        ])
        .env("RUST_LOG", "info")
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        output.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("expression depth exceeds"),
        "must skip recursive normalization: {stdout}"
    );
    assert!(stdout.contains("lifted invariant passed"), "{stdout}");
    assert!(stdout.ends_with("UNSAT\n"), "{stdout}");
}

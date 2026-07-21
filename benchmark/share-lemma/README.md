# Portfolio lemma-sharing evaluation

A/B evaluation of `--share-lemma` for the `ic3_seeds` portfolio (12 IC3 workers
differing only by random seed). It backs two commits:

- **import + deadlock fix** — IC3 now consumes inbound shared lemmas; fixes a
  worker↔manager IPC deadlock the wiring exposed.
- **finite-frame lemma sharing** — workers export short finite-frame lemmas
  (not just late `k=None` invariants), which is where the speedup comes from.

## Benchmarks

HWMCC'24 aiger track, from <https://zenodo.org/records/14156844>:

- `benchmarks_aiger.tar.gz` — the models (top-level `aiger/…` prefix)
- `hwmcc24_results_aiger.csv` — per-solver competition results, used only to
  pick difficulty-graded subsets

The models are **not** vendored here (~1 GB). Fetch and extract them, then point
`run_ab.sh` at the directory. The lists under `lists/` name the exact
benchmarks used (paths relative to the `aiger/` root).

Subsets were chosen with `select_benchmarks.py` — family-diversified, in a
difficulty band defined by the best competition `time_cpu` — and are UNSAT
(safe) except `sat_soundness.txt`, which is SAT (unsafe) and used only to check
that sharing never reports a false UNSAT.

## Reproduce

```sh
cargo build --release

# fetch + extract the aiger models into ./models (see link above), then:
BENCH=$(pwd)/benchmark/share-lemma
bash $BENCH/run_ab.sh $BENCH/lists/medium_unsat.txt ./models 60  medium.csv
bash $BENCH/run_ab.sh $BENCH/lists/hard_unsat.txt   ./models 120 hard.csv
python3 $BENCH/summarize.py medium.csv hard.csv
```

`run_ab.sh` runs each benchmark twice (baseline vs `--share-lemma`) under the
timeout and writes `benchmark,cond,result,wall_s`. `RIC3_SHARE_FINITE_MAXLEN=0`
restricts sharing to inductive invariants only (the import-only configuration).

## Results (16-core machine; `ic3_seeds` ×12)

Machine solves the models much faster than the competition hardware, so
timeouts here are short. Raw CSVs are in `results/`.

### Import wiring alone is not enough (`results/baseline_vs_import_only_60s.csv`)

Sharing only `k=None` inductive invariants — 18 medium UNSAT cases, 60 s:

| | solved |
|---|---|
| baseline | 12 / 18 |
| share (invariants only) | 12 / 18 |

Net **+0**. Those invariants arrive too late to help. This is what motivated
finite-frame sharing. (This configuration also first surfaced, then fixed, the
IPC deadlock — before the fix it *regressed* to 10/18 with intermittent hangs.)

### Finite-frame sharing (`results/baseline_vs_finite_*.csv`)

Same 27 UNSAT cases (18 medium @60 s, 6 + 4 hard @120–150 s):

| | solved | notes |
|---|---|---|
| baseline | 19 / 27 | |
| share (finite-frame), single run | 21 / 27 | what the `results/` CSVs record |
| share (finite-frame), **reliable** | **20 / 27** | **+1**, after re-verification |

Wall time on commonly-solved cases: **−21 % to −27 %**; 6 cases notably faster,
none slower.

The raw CSVs show two flips (`+2`), but single-run case counts are noisy with 12
random seeds, so only repeat-verified results are claimed. `summarize.py` on the
`results/` CSVs prints the single-run `+2`; the reliable figure is `+1`:

- **+1 solved, reliable** — `processed_hl_arr_access_128_bv`: baseline times out
  5/5 at 60 s → sharing solves **5/5 in ~0.4 s**.
- **Speedups (each confirmed over ≥4 runs)** — `byte_add_1-1` 7.2 s → 0.2 s
  (~36×), `qspiflash_dualflexpress_divfive-p027` 13.3 s → 0.1 s, `zonotope_2`
  38 s → 10.6 s, `93.c` 5 s → 0.1 s, `ILA_Piccolo_JALR_sanity` 42 s → 19 s.
- `rocket_1951` solved once at 108 s but timed out on re-runs — high variance
  near the boundary, **not** counted as a reliable win.

### Soundness (`lists/sat_soundness.txt`)

6 SAT (unsafe) cases under `--share-lemma`: all return SAT or time out, **never a
false UNSAT** — importing shared lemmas does not report an unsafe design as safe.

### Soundness scope

Sharing is only sound between workers that reason over the *same* transition
system. Two guards enforce this (see "make lemma sharing sound for heterogeneous
configs"):

- **Same-group routing** — finite-frame lemmas are shared only among workers
  whose config matches after dropping `--rseed`. Different preprocessing/config
  ⇒ different frame semantics ⇒ not shareable.
- **Share-safe engines only** — `--inn` (unrolls to internal signals), `--abs-*`
  and `--pred-prop` transform the system; their lemmas are not valid clauses in
  the original variable space, so those engines abstain from sharing entirely.
  Without this guard, a mixed `ic3 + ic3 --inn` ensemble reported a **false
  UNSAT** on an unsafe design ~50% of runs (always via the `--inn` worker).

`ic3_seeds` is a single share-safe group, so it shares fully and soundly.

## Files

- `run_ab.sh` — baseline-vs-share A/B runner
- `select_benchmarks.py` — pick difficulty-graded, family-diverse subsets
- `summarize.py` — solved counts, flips, speedups from result CSVs
- `lists/` — the exact benchmarks used
- `results/` — raw result CSVs from the runs above

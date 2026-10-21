# Reachable-state guided generalization in rIC3

This note covers the design, implementation and evaluation of an experimental
IC3 extension on branch `feature/reachable-cache`. It is based on `master` at
`d513ec2`. The extension follows the public QUIP idea (A. Gurfinkel and
A. Ivrii, *Pushing to the Top*, FMCAD 2015) and adds a cache of concrete
reachable states.

## 1. Motivation

IC3 learns lemmas that are inductive relative to a low frame. Some of them are
violated by states that are reachable only deeper down. Such a lemma can never
be part of an inductive invariant, and the solver keeps paying for it:

* during generalization, MIC accepts the over-general candidate;
* during propagation, every attempt to push the lemma fails, and with `--ctp`
  each failure also starts extra blocking work.

A *concrete reachable state* is a cheap certificate against such lemmas. The
extension collects reachable states on the side and uses them in MIC, in
propagation, and to drive the search for more of them.

## 2. Design

### 2.1 Reachable-state cache (`ReachCache`, `src/ic3/reach.rs`)

* **Contents.** Each entry is an assignment to the latches, stored as two bit
  vectors (`val`, `known`), so an entry can be partial. The entry also records
  its *depth* `d`: the state is reachable in at most `d` steps. Every entry is
  built from a concrete chain of transitions that starts in an initial state,
  and the constraints hold at every step of that chain. Depth-0 entries (the
  initial states themselves) are not stored, because `cube_subsume_init`
  already covers them.
* **Index.** There is one bucket per literal. `bucket[l]` lists the states that
  satisfy `l`.
* **Lookup.** `find(cube, max_depth)` takes the smallest bucket among the
  cube's literals and stops at once if that bucket is empty. It then scans
  the bucket, testing each state with bit operations. An unknown bit never
  matches, which keeps lookups conservative. The cost is
  `O(|cube| + |smallest bucket| * |cube|)`. On the benchmarks a lookup scans
  about 25–40 states on average, much less than one SAT call.
* **Management.** Each entry has a hit count and a last-use timestamp.
  Cleanup runs when the cache is full and does three things. It adapts the
  capacity between `--reach-cap-min` (40) and `--reach-cap-max` (1000): the
  capacity doubles if at least half of the entries were hit since the last
  cleanup, and halves if fewer than one eighth were. It keeps the hottest and
  most recently used entries, up to 3/4 of the capacity. It halves all hit
  counts, which ages them. The total number of bucket entries is kept below
  2^25, so on designs with many latches the maximum capacity shrinks.

### 2.2 Uses of the cache

Let `s` be a cached state of depth `d`, and let `F_i` be IC3's frame `i`.
IC3 frames over-approximate the states reachable in at most `i` steps, so
`s ∈ F_i` for every `i ≥ d`.

1. **MIC restriction (`--reach-mic`).**
   * *Candidate rejection.* In `down` and `ctg_down`, a candidate cube that
     contains a cached state is treated as a failed drop, and no SAT call is
     made.
   * *Core refinement.* Every inductive core is post-processed. This covers
     the core of the obligation, the cores returned by `down` and `ctg_down`,
     the cores from `push_lemma`, the propagation cores, and the cores of CTG
     lemmas. Let `c` be the cube whose relative-induction check succeeded and
     `k ⊆ c` its core. Every cube `k ⊆ d ⊆ c` is still relatively inductive:
     `F ∧ ¬d ∧ T ∧ d'` implies `F ∧ ¬c ∧ T ∧ k'`, which is UNSAT. So if `k`
     contains a cached state, literals of `c` that the state violates are
     added back until no cached state is left in the cube. These are the
     "re-added literals" of the idea.
   * *Modes.* By default, states of any depth are used. This is the QUIP
     heuristic: prefer lemmas that can reach the top. With
     `--reach-mic-exact true`, only states with `d ≤ frame` are used. In that
     mode the rejected candidates would have failed their SAT check anyway, so
     the mode only saves SAT calls. It also yields a free soundness check:
     `exact_violation` counts cores of frame `i` that contain a state with
     `d ≤ i`. That cannot happen if the cache is correct, and the counter was
     0 in every run.
2. **Push skipping (`--reach-push`).** A push of a lemma into `F_i` is skipped
   when a cached state with `d ≤ i` lies in the lemma's cube. Such a push is
   guaranteed to fail: the first state on the path to `s` that lies in the
   cube has a predecessor in `F_{i-1}`. Skipping it therefore never loses a
   push. This applies to `push_lemma` after generalization and to
   `propagate`. Pushing to the infinite frame (`propagate_to_inf`) is skipped
   when a cached state of any depth lies in the cube. That is exact too,
   because the infinite frame is an inductive invariant.
3. **Closing may obligations.** A may obligation whose cube contains a cached
   state is closed at once, and the witness chain is extended from that state
   (see below).

### 2.3 May-proof obligations (`--may-po`)

* **Creation.** In `generalize`, an ordinary obligation `po` is blocked,
  generalized to `mic`, and `mic` is pushed up to frame `k` (the push into
  `F_k` fails). If generalization dropped at least `--may-po-min-shrink`
  literals (default 2, that is "more than one literal") and `k ≤ level`, a
  *root* may obligation `(mic, k)` is created. It is not created when `mic`
  already contains a cached state. Each root has an id. Later obligations
  derived from it carry the id and stop as soon as the root is retired.
* **Queue and budget.** May obligations live in a separate
  `ProofObligationQueue`. Each processed ordinary obligation earns
  `--may-po-share` (default 0.2) credits, capped at 16. One may obligation is
  processed per credit, interleaved with the ordinary queue. The may queue
  holds at most 4096 entries, and lowest-priority entries are dropped first.
  A may obligation is dropped after 10 retries, mirroring `drop-po`.
* **Processing.** This mirrors `block()`, with four differences:
  * when the cube intersects `Init`, or contains a cached state, the root is
    retired and a witness is computed;
  * may obligations never produce a counterexample;
  * lemmas learned while blocking them are ordinary, sound lemmas, recorded
    with `po = None` so that propagation never moves a may obligation into the
    must queue;
  * they never create new roots.
* **Witnesses.** The chain `po → po.next → … → root` holds a cube per step,
  and every state of a cube has a successor in the next cube, as predecessor
  lifting guarantees. Concrete states are computed with dedicated GipSAT
  solvers that contain only `T` and the constraints; one of them also has
  `Init`. The query is `s_i ∧ next(cube_{i+1})`, solved with the decision
  domain set to all current and next latches and the inputs. The domain makes
  GipSAT's domain restriction return a total successor state. When the chain
  starts at `Init`, the first query is `cube_0 ∧ next(cube_1)` on the solver
  with `Init`. Each successor is stored with depth `i`, or with `d + i` when
  the chain started at a cached state of depth `d`. A failed query (never
  observed) just ends the chain, and nothing unsound is stored.

### 2.4 Variant: random-walk seeding (`--reach-sim N`)

After frame 0 is built, the cache is seeded with `N` states from random walks
of length 32. Each step is one cheap successor query on the plain `T` solver,
with random input values and random values for uninitialized latches. If the
random values contradict the constraints, the query is retried without them.

### 2.5 Integration and interactions

* **CTG.** `ctg_down` gets candidate rejection and core refinement. CTG lemmas
  (`trivial_block`) get core refinement.
* **Parent lemma, dynamic, MAB.** These are untouched. They only change the
  literal order and the parameters. May-obligation generalization uses
  `MicType::from_config`.
* **drop-po.** May obligations have their own activity limit.
* **GipSAT domain restriction.** MIC keeps its restricted domain. The witness
  solvers use an explicit full latch domain so that the states they return
  are total.
* **Incompatible options.** `--inn`, `--abs-cst`, `--abs-trans` and
  `--pred-prop` are rejected together with the reach flags (`validate`). They
  change what the frames mean.
* **Default behaviour.** With all reach flags off, `reach` is `None`, and
  every hook returns at once after a field test. The only additions are two
  counters (`push`, `propagate_push`).

### 2.6 Flags

| flag | default | meaning |
|---|---|---|
| `--reach-cache` | off | turns on `reach-mic`, `reach-push` and `may-po`, unless they are set explicitly |
| `--reach-mic <bool>` | off (on with `--reach-cache`) | MIC candidate rejection and core refinement |
| `--reach-mic-exact <bool>` | false | use only states with depth ≤ frame in MIC |
| `--reach-push <bool>` | off (on with `--reach-cache`) | skip pushes that are known to fail |
| `--may-po <bool>` | off (on with `--reach-cache`) | may-proof obligations, which feed the cache |
| `--may-po-share <f>` | 0.2 | may obligations per ordinary obligation |
| `--may-po-min-shrink <n>` | 2 | minimum number of literals generalization must drop to create a may root |
| `--reach-sim <n>` | 0 | random-walk seeding |
| `--reach-cap-min/max` | 40/1000 | adaptive cache capacity |

### 2.7 Files

* `src/ic3/reach.rs`: new. Cache, may obligations, witnesses, seeding, hooks,
  unit tests.
* `src/ic3/mod.rs`: flags, validation, fields, statistics output.
* `src/ic3/block.rs`: may interleaving in `block`, `may_create`, push skipping
  and core refinement in `push_lemma`, `generalize` and `trivial_block`.
* `src/ic3/mic.rs`: candidate rejection and core refinement in `down` and
  `ctg_down`.
* `src/ic3/propagate.rs`: push skipping, core refinement, and skipping
  hopeless pushes to the infinite frame.
* `src/ic3/proofoblig.rs`: `may_root`, `add_if_absent`, `ready`, `len`,
  `pop_lowest`.
* `src/ic3/utils.rs`: push counters.
* `scripts/reach-bench/`: the benchmark runner (`shard.py`), the summary
  script (`summarize.py`), the certificate check (`certify.sh`), and
  `cert-fixes/`, two patches for bugs in certificate export that are
  unrelated to this work (Section 4).


## 3. Benchmark setup

* **Machine.** Shared 16-core host with 30 GB of RAM. At most 4 solver
  processes ran at a time: 3 during the first stage, 4 afterwards. Each run
  had a 300 s wall-clock limit and a 6 GiB `RLIMIT_AS` cap, and used the
  `solver-benchmark/script/run.py` harness, which sends SIGINT at the
  deadline and SIGKILL 5 s later. Configurations were run back to back on the
  same case and worker.
* **Binaries.**
  * `base`: `master` at `d513ec2`, built without changes.
  * `R*`: this branch at `65eac90`, built the same way.
  * An early build (`reach`, `v1`) had the partial-state bug described in
    Section 5. It is reported only where it is labelled.
  * Without any reach flag, the new binary is identical to `base`: same
    answers and the same 15/30 solved cv32e40x cases, with run times within
    1%.
* **IC3 options.** rIC3's default `ic3` options (CTG on, `drop-po` on,
  parent lemma on), plus the flags under test.
* **Case selection** (HWMCC'25 bit-level safety, 330 models):
  * all 30 `cv32e40x` models;
  * a 30 s `base` screen of the other 300 models. It gave 96 models solved in
    under 1 s, 63 in 1–30 s, 136 unsolved, and 5 that ran out of memory;
  * the *main* set: the 30 cv32e40x models, 25 random models from the
    1–30 s group and 20 random models from the unsolved group (75 cases);
  * the *stage-2* set, used for seeds and ablations: the 30 cv32e40x models
    plus the 33 other main-set models that `base` or `reach` solved in the
    first stage (63 cases). Main-set models that every configuration left
    unsolved were dropped there to save time.
  * the *extension* set: 60 more random models from the screen's unsolved
    group (`base` vs `R`, seed 0).
* **Measures.** Solved count, PAR-2 (mean seconds, unsolved counted as 600 s),
  and IC3 internals parsed from the statistics that rIC3 prints at exit
  (rIC3 also prints them on SIGINT).

## 4. Soundness checks

* **Verdicts.** No run disagreed with any other on SAT/UNSAT, across about
  1,900 runs (all configurations, seeds and builds).
* **Exactness counter.** `exact_violation` was 0 in every final-build run, in
  both modes, including runs seeded by random walks. In the buggy early
  build it was not 0 (Section 5).
* **Certificates (certifaiger).** Certifaiger was built from source at
  `ba86b45`, because the Docker image that rIC3 expects is not available
  here. Two bugs on `master` that are unrelated to this work block
  certificate export, and they affect `base` in the same way:
  1. `Aig::reencode` in `aig-rs` leaves the constant node unmapped. Any
     witness with a latch whose next state is constant then fails to encode
     ("reference outside graph"), and rIC3 panics while printing the
     certificate. This happened on 8 of 24 sampled models, `cal40` among
     them.
  2. The first input line of a counterexample trace contains only the inputs
     that were assigned.

  A validation build with both fixes passes certifaiger on every certificate
  that `R` produced for the cases it solves in under 60 s (stage-2 set plus
  extension): 33/33 UNSAT witness circuits and 16/16 SAT traces. The trace fix
  in `scripts/reach-bench/cert-fixes/rIC3-frontend.patch` writes lines over
  the original AIGER inputs and latches. Before it, 9 of the 16 traces were
  rejected for lines that were too short, `base` included.

## 5. A bug found during the evaluation: partial witness states

The first implementation (`v1`) read the successor state from GipSAT models
on the solver constrained by `Init`. With domain restriction, that model left
many next-state literals unassigned: 12 of 44 on `microban_132`. The next
query then completed the partial state arbitrarily, so some cached "reachable"
states were not reachable. The `exact_violation` counter found this: random
walks produced cores at frame `i` that contained a state of depth ≤ `i`.

The fix (`65eac90`) has three parts:
* chains start from the *total* initial state;
* every successor query is made from a total state;
* only total successor states are kept.

The cache can only make IC3 avoid work or keep more literals in a lemma, so
the bug never threatened soundness. It did make `v1`'s heuristic decisions
partly arbitrary. All numbers below come from the fixed build unless they are
labelled `reach (v1)`.

## 6. Results

### 6.1 Headline (stage-2 set, 63 cases, 300 s, 3 seeds)

| config | solved (seed 0/1/2) | mean solved | PAR-2 (seed 0/1/2) | mean PAR-2 |
|---|---|---|---|---|
| base | 47 / 47 / 47 | 47.0 | 175.8 / 178.9 / 180.0 | 178.2 |
| R (`--reach-cache`) | 49 / 50 / 51 | **50.0** | 156.6 / 152.0 / 147.8 | **152.1** |

The stage-2 set split into its two parts:

| subset | base solved (mean) | R solved (mean) | base PAR-2 | R PAR-2 |
|---|---|---|---|---|
| cv32e40x (30) | 15.3 | 17.3 | 311.5 | 281.0 |
| other (33) | 31.7 | 32.7 | 57.1 | 35.0 |

Every seed of R solves more cases than every seed of `base`. As totals over
63 cases, `base` scores 11,074 penalized seconds and `R-exact` scores 9,525.

**Noise caveat.** Changing only the seed moves `base` by ±2–3 cases on
cv32e40x (Table 6.3). The per-case gains and losses below have to be read
against that.

### 6.2 Extension (60 harder models, seed 0)

| config | solved | safe | unsafe | PAR-2 |
|---|---|---|---|---|
| base | 15 | 8 | 7 | 475.8 |
| R | 19 | 11 | 8 | 438.0 |

* R solves 5 models that `base` does not:
  * `rast-p20`: 227 s;
  * `rocket_1937`: 71 s;
  * `ILA_Piccolo_LUI_sanity`: 74 s;
  * `Problem05_label47+token_ring.13.cil-2`: 69 s;
  * `example_162_miter`: 30 s.
* R loses `elevator_spec2_product25`, which `base` solves in 299 s.
* R ran out of memory once, on `ILA_Flute_BLT_problem` under the 6 GiB local
  cap. `base` timed out on that model.

### 6.3 cv32e40x per case (seconds; TO = 300 s timeout; seeds 0/1/2)

| case | base | R |
|---|---|---|
| p129 | 89 / TO / TO | TO / 31 / 13 |
| p131 | TO / TO / 220 | 167 / 244 / 119 |
| p144 | 76 / 78 / 70 | 121 / 104 / 178 |
| p18 | TO / TO / TO | TO / TO / 259 |
| p256 | TO / TO / TO | 125 / TO / TO |
| p472 | TO / 9 / 82 | 24 / 26 / 7 |
| p568 | 73 / 109 / 173 | 38 / 17 / TO |
| p585 | TO / TO / TO | 48 / TO / TO |
| p608 | 25 / TO / TO | 53 / 162 / 82 |
| p667 | 64 / 57 / 37 | TO / 133 / TO |
| p743 | TO / 261 / 92 | TO / TO / 152 |
| p767 | TO / TO / TO | TO / TO / 253 |
| p88, p228, p530, p114, p151, p189, p193, p524 | TO in all | TO in all |

The remaining cv32e40x cases are solved in under 30 s by both. In short:

* **Consistent gains.** p131 (R solves 3/3 seeds, `base` 1/3), p608 (3/3 vs
  1/3) and p472 (3/3 vs 2/3).
* **Consistent loss.** p667 (1/3 vs 3/3). p144 is also slower with R.
* **Unsolved.** p88, p228 and p530 stay unsolved within 300 s for every
  configuration.

### 6.4 Ablation (stage-2 set, seed 0)

| config | flags | solved | PAR-2 |
|---|---|---|---|
| base | — | 47 | 175.8 |
| R | `--reach-cache` | 49 | 156.6 |
| R-exact | `--reach-cache --reach-mic-exact true` | **51** | **151.2** |
| R-nomic | `--reach-cache --reach-mic false` | 48 | 169.7 |
| R-nopush | `--reach-cache --reach-push false` | 48 | 169.0 |
| R-mayonly | `--may-po true` (cache only closes may obligations) | 50 | 158.5 |
| R-nomaymic | `--reach-cache --may-po-mic false` | 47 | 179.6 |
| R-sim | `--reach-cache --reach-sim 512 --reach-sim-len 64` | 49 | 165.5 |
| R-simonly | `--reach-mic true --reach-push true --reach-sim 512 --reach-sim-len 64` | 45 | 196.4 |
| reach (v1, buggy witnesses) | `--reach-cache` | 49 | 162.8 |

### 6.5 Internals (R, stage-2 set, seed 0, summed over 63 cases)

* **SAT calls.** 33.6 M for R vs 39.5 M for `base`. MIC calls are about the
  same: 1.20 M vs 1.17 M.
* **Cache lookups.** 29.0 M lookups, 0.87 M hits (3.0%), and 20 states
  scanned per lookup on average. One lookup costs a few hundred bit tests,
  which is negligible next to a SAT call. The largest cache reached 1,000
  states (the cap). On cv32e40x the cache typically holds 50–300 states.
* **MIC.**
  * Candidate rejections: 0.73 M, which is 4.1% of the 17.6 M MIC SAT checks
    (`down`).
  * Literals re-added to cores: 14.8 k.
* **Pushes skipped.** 104 k, against 2.18 M failed pushes in propagation
  (4.8%). Another 269 pushes to the infinite frame were skipped.
* **May obligations.**
  * 339 k roots created, 147 k may steps processed;
  * 49 k blocked (each giving a sound lemma);
  * 322 reached `Init`, 7.5 k closed by the cache;
  * most of the rest were dropped by the queue cap or the retry limit.
* **Witnesses.** 18.7 k successor queries, none failed. They produced
  18.3 k states.

## 7. Analysis

1. **What helps most is the may obligations, not the cache.** May
   obligations alone (`R-mayonly`, where the cache only closes may obligations)
   already get most of the gain: 50 solved, PAR-2 158.5. Their benefit needs
   their lemmas to be generalized: `R-nomaymic` falls back to `base` level
   (47 solved). Blocking a may obligation adds a strong lemma at the frame
   where an earlier lemma failed to push, which is the "pushing to the top"
   effect. The clearest example is `rast-p16`. `base` keeps adding frames
   (more than 1,260) until it runs out of memory, while every may-obligation
   configuration converges in about 1 s at frame 276.
2. **The cache uses add a small, plausible gain that is within the noise.**
   Removing MIC restriction or push skipping costs about one case and about
   13 PAR-2 points at seed 0. Push skipping and exact-mode MIC can only save
   work, so it is not surprising that `R-exact` is the best configuration.
   The QUIP-style aggressive MIC restriction (states of any depth) is not
   better than exact mode here.
3. **The cache is small.** Only about 1 in 1,000 may obligations reaches
   `Init`, and most cached states come from extending chains out of cached
   states. Hit rates of about 3% mean that each use removes only around 5%
   of its target work.
4. **Random-walk seeding hurts.** `R-simonly` solves 45 and `R-sim` 49 with
   a worse PAR-2. Shallow random states make MIC re-add many literals
   (102–154 k core refinements, against 15 k from witness states). That
   biases lemmas against states which are harmless to exclude at low frames.
5. **The trajectories are chaotic.** IC3 is very sensitive to perturbation.
   Seeds alone move `base` by ±3 cases on cv32e40x. The overall improvement
   (+3 solved, −15% PAR-2 across 3 seeds, +4 on the hard extension) is
   consistent. Individual cv32e40x wins and losses mostly are not, apart from
   p131, p472, p608 (gains) and p667 (loss).

## 8. Is this paper material?

Not yet as it stands. The ingredients (may obligations, reachable states) are
QUIP's. The measured effect is a modest, fairly consistent gain from may
obligations, plus marginal gains from the cache. What would strengthen it:

* **Scale.** The full HWMCC'24/'25 bit-level tracks at the official 3600 s
  limit, several seeds, and the portfolio context (does it add a unique
  solve to rIC3's portfolio?). This is planned on the solver-benchmark CI.
* **A sharper contribution beyond QUIP.** Candidates:
  * a budget that adapts the may-obligation share online, as the bandit
    style of `--mab` does;
  * using cached states to *rank* MIC literal orders, rather than only to
    reject candidates;
  * cheaper witness extraction (the ternary-simulation successor), so that
    many more reachable states are collected;
  * exploiting the depth-exact certificates to prune CTG.
* **Mechanism evidence.** Lemma-lifetime statistics: how many lemmas are
  later found non-inductive, and how far they are pushed, for `base` vs R.

## 9. Next steps

1. Run the full bit-level safety track on the briareus CI
   (`experiment/reachable-cache` in solver-benchmark): `base`, R, R-exact
   and R-mayonly.
2. If the gain holds, tune `--may-po-share` and `--may-po-min-shrink`, and
   try an adaptive share.
3. Upstream the two certificate-export fixes separately.
4. Investigate the p667 and p144 slow-downs (more MIC work from may
   obligations on cases that `base` already solves fast).

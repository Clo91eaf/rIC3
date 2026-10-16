# rIC3 Hardware Model Checker

[![License](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
[![CI](https://github.com/gipsyh/rIC3/actions/workflows/ci.yml/badge.svg)](https://github.com/gipsyh/rIC3/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/rIC3.svg?logo=rust)](https://crates.io/crates/rIC3)
[![Docker](https://img.shields.io/docker/v/gipsyh/ric3?label=Docker&logo=docker)](https://hub.docker.com/r/gipsyh/ric3)

### LLM-Assisted Model Checking
rIC3 supports LLM-accelerated model checking through invariant generation. For details, see the paper [CIll: CTI-Guided Invariant Generation via LLMs for Model Checking](https://arxiv.org/abs/2602.23389).
The prompt and VCD inspection MCP tools are located under the `tools` directory. For a concrete example, see https://github.com/gipsyh/cill-exp

The `master` branch of CIll is an actively developed version and highly unstable; development has been put on hold due to time constraints. [cill-exp](https://github.com/gipsyh/cill-exp) contains the link of relatively stable version.

<p align="center">
	<img width="500" height="auto" src="./images/CIll.svg" style="display:inline-block;">
</p>

### HWMCC
rIC3 achieved first place in both the bit-level track and the word-level bit-vector track at the 2024 and 2025 Hardware Model Checking Competition ([HWMCC](https://hwmcc.github.io)).


### rIC3 Tool Flow
<p align="center">
	<img width="500" height="auto" src="./images/toolflow.svg" style="display:inline-block;">
</p>

### Install From Crates.io
```cargo install rIC3```

### Install From Source
rIC3 can be compiled on both Linux and macOS.

- Install the Rust compiler
- Clone the repository: `git clone --recurse-submodules https://github.com/gipsyh/rIC3`
- Install Bitwuzla from `https://github.com/bitwuzla/bitwuzla` (required by `wlbmc`)
- Install Yosys from `https://github.com/YosysHQ/yosys` and Yosys-Slang from `https://github.com/gipsyh/yosys-slang/tree/ric3` (required by the project-based flow and CIll)
- Build `cd rIC3 && cargo b --release`
- Run `cargo r --release -- check <AIGER/BTOR> portfolio`
- Install `cargo install --path .`

### Usage
- Project-based RTL flow: if your design directory contains a `ric3.toml`, run verification directly from that directory with `ric3 run`.

  ```toml
  [dut]
  # Top-level module name
  top = "counter"
  # RTL source files used to build the DUT
  files = ["counter.sv"]
  # Reset signal name; prefix with "!" for an active-low reset
  reset = "!rst_n"
  ```

  For complete runnable examples, see `examples/`.

- Direct AIG/BTOR checking:
  - 16-threads Portfolio ```ric3 check <AIGER/BTOR> portfolio```
  - single-thread IC3 ```ric3 check <AIGER/BTOR> ic3```

- Experimental proof-based abstraction for IC3 (off by default):

  ```sh
  ric3 check model.btor2 ic3 --pba --pba-depth 18 --pba-time-limit 30 --time-limit 300
  ```

  After parsing/bit-blasting, PBA follows the observed JasperGold 2021.03
  proof-selection flow. Each round proves that no bad state occurs anywhere
  in the bounded prefix, walks the UNSAT proof back to its original clauses,
  and marks their source state, input and gate nodes. It completes paths to
  the property, constraints and selected next-state roots. Unselected nodes
  encountered on those paths become shared per-cycle inputs. Known cut-node
  initial values are guarded by a first-cycle pulse; unknown values stay free.
  Relational BTOR initializers are retained as relations.

  Each round replaces the previous selection, so refinement can remove nodes.
  An incremental BMC probe checks the next ten frames with a shared 10,000
  conflict budget; a leak triggers a fresh concrete prefix proof at that depth.
  An inconclusive probe hands the model to IC3. Before the existing COI,
  CNF/BVE, SCORR and FRTS preprocessing, the abstraction is rebuilt through
  the BTOR frontend's word-level simplification and Boolean encoding. This
  preserves XOR/XNOR structure and gives IC3 the same encoding as a standalone
  one-bit BTOR export. `--pba-normalize false` disables this step; opaque or
  nonfunctional CNF definitions retain their original representation. A
  conservative expression-depth check also keeps deep or wide definitions in
  CNF, avoiding stack overflow in recursive frontend passes. Abstract IC3 traces
  are replayed on the concrete system; spurious traces trigger the same fresh
  selection process. `--pba-refine-limit` (default 8) caps IC3 restarts before
  concrete fallback. Bounded UNSAT never establishes unbounded safety.

  Proof cores are rechecked with up to four fresh proofs to remove avoidable
  dependencies. Every selected abstraction is checked against its bounded prefix. Abstract SAFE results require a lifted
  certificate to pass concrete initiation and induction checks. `--cert` and
  `--cex` refer to the concrete model. `--pba-dump-dir DIR` saves each round's
  model, proof seeds, completed selection and concrete projection, plus the
  normalized IC3 model and its projection. Renumbered inputs and states use
  explicit projections; auxiliary gates and the first-cycle pulse are fresh
  when lifting the proof to the concrete model.

  The 30-second PBA budget covers the preparation loop and caps each later
  refinement preparation; `--time-limit` is shared by preparation, IC3,
  replay and proof validation. `--pba-depth` defaults to 18 (maximum 128).
  A zero PBA budget skips abstraction. CNF growth is capped at two million
  actually encoded SAT variables and eight million clauses. Completed concrete
  witnesses are checked step by step against the original unflattened CNF.
  Existing IC3 preprocessing may delay cancellation during construction.

  Implementation references are recorded beside the corresponding functions:
  JG proof query `0x8b47d0`, original-clause visitor `0x991a30`, path completion
  `0x8aa620`, rewriting `0x8ac740`, and leak probing `0x8cc510`. The constructor
  is regression-checked against nine captured p530 selections, including the
  final 310 source latches, 352 gate cuts and 795 total cuts. This checks model
  construction with recorded seeds; autonomous CaDiCaL proof selection is
  different from JG's SAT backend and does not promise the same seeds or time.
  The optional real-capture test uses `RIC3_JG_CAPTURE` (see `src/pba/captured.rs`).
  A paired-export regression compares the normalized CNF, including clause
  order, against the standalone BTOR frontend (`RIC3_PBA_NORMALIZE_MODEL` and
  `RIC3_PBA_NORMALIZE_BTOR`, see `src/pba/normalize.rs`).
  PBA supports standalone IC3 without lemma exchange or IC3 local proofs.
  Library callers use `create_bl_engine` or `pba::PbaEngine`, not `IC3::new`.

### Docker
- build image: ```docker build -t ric3 .```
- run: ```docker run -v <AIGER/BTOR>:/model.<aig/btor> ric3 check model.<aig/btor> portfolio```

### Publications
- [CAV2025] [The rIC3 Hardware Model Checker](https://doi.org/10.1007/978-3-031-98668-0_9)
- [CAV2025] [Deeply Optimizing the SAT Solver for the IC3 Algorithm](https://doi.org/10.1007/978-3-031-98668-0_12)
- [DAC2024] [Predicting Lemmas in Generalization of IC3](http://doi.org/10.1145/3649329.3655970)
- [arXiv] [Extended CTG Generalization and Dynamic Adjustment of Generalization Strategies in IC3](https://arxiv.org/abs/2501.02480)
- [arXiv] [CIll: CTI-Guided Invariant Generation via LLMs for Model Checking](https://arxiv.org/abs/2602.23389)


Copyright (C) 2023 - Present, Yuheng Su (gipsyh.icu@gmail.com). All rights reserved.

#!/usr/bin/env python3
"""Run solver-benchmark/script/run.py on a case list in N parallel shards.

usage: shard.py CONFIG.json CASELIST OUTDIR [--jobs 4] [--time-limit 300] [--solvers a b ...]
Each shard is one sequential run.py process (all solvers of a case run back to
back on the same shard), so at most `jobs` solver processes run at once.
"""
import argparse, subprocess, sys
from pathlib import Path

BENCH = Path("/root/yjh-workspace/solver-benchmark")

ap = argparse.ArgumentParser()
ap.add_argument("config")
ap.add_argument("cases")
ap.add_argument("outdir")
ap.add_argument("--jobs", type=int, default=4)
ap.add_argument("--time-limit", type=float, default=300)
ap.add_argument("--memory-mb", type=int, default=6144)
ap.add_argument("--solvers", nargs="+")
a = ap.parse_args()
cases = [c.strip() for c in Path(a.cases).read_text().splitlines() if c.strip()]
out = Path(a.outdir).resolve()
out.mkdir(parents=True, exist_ok=True)
procs = []
for j in range(a.jobs):
    mine = cases[j::a.jobs]
    if not mine:
        continue
    cmd = [sys.executable, str(BENCH / "script/run.py"), "--config", str(Path(a.config).resolve()),
           "--pattern", ",".join(mine), "--time-limit", str(a.time_limit),
           "--memory-mb", str(a.memory_mb), "--output", str(out / f"shard{j}")]
    if a.solvers:
        cmd += ["--solvers", *a.solvers]
    log = open(out / f"shard{j}.log", "w")
    procs.append(subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT))
rc = 0
for p in procs:
    rc |= p.wait()
print("done", rc)

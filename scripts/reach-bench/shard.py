#!/usr/bin/env python3
"""Run solver-benchmark/script/run.py on a case list with N parallel workers.

usage: shard.py CONFIG.json CASELIST OUTDIR [--jobs 4] [--time-limit 300]
                [--solvers a b ...] [--seed N]
Workers pull cases from a shared queue; for each case one sequential run.py
process runs all selected solvers back to back, so at most `jobs` solver
processes run at once.
"""
import argparse, subprocess, sys, threading
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
ap.add_argument("--seed", type=int)
a = ap.parse_args()
cases = [c.strip() for c in Path(a.cases).read_text().splitlines() if c.strip()]
out = Path(a.outdir).resolve()
out.mkdir(parents=True, exist_ok=True)
lock = threading.Lock()
queue = list(enumerate(cases))
rc = [0]


def worker(j):
    log = open(out / f"shard{j}.log", "a")
    while True:
        with lock:
            if not queue:
                return
            i, case = queue.pop(0)
        cmd = [sys.executable, str(BENCH / "script/run.py"), "--config", str(Path(a.config).resolve()),
               "--pattern", case, "--time-limit", str(a.time_limit),
               "--memory-mb", str(a.memory_mb), "--output", str(out / f"case{i:04d}")]
        if a.seed is not None:
            cmd += ["--seed", str(a.seed)]
        if a.solvers:
            cmd += ["--solvers", *a.solvers]
        log.flush()
        r = subprocess.call(cmd, stdout=log, stderr=subprocess.STDOUT)
        with lock:
            rc[0] |= r


threads = [threading.Thread(target=worker, args=(j,)) for j in range(a.jobs)]
for t in threads:
    t.start()
for t in threads:
    t.join()
print("done", rc[0])

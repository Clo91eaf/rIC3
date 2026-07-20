#!/usr/bin/env python3
"""Select benchmark subsets for the lemma-sharing A/B from the HWMCC'24 results.

Reads the competition per-solver results CSV (columns: benchmark, solver,
result, time_real, time_cpu, memory) and emits family-diversified lists of
benchmarks in a chosen difficulty band. "Difficulty" is the best (minimum)
time_cpu any solver needed; a benchmark nobody solved is excluded.

Usage:
  select_benchmarks.py <results_aiger.csv> <result: sat|unsat> \\
      <min_cpu_s> <max_cpu_s> <max_per_family> <count> [--only PATHS_FILE]

  --only limits selection to benchmarks whose path appears in PATHS_FILE (e.g.
  the `tar tzf` listing of the aiger tarball), so you only pick cases you have.

The HWMCC'24 results CSV and aiger benchmarks are at
https://zenodo.org/records/14156844 (file hwmcc24_results_aiger.csv and
benchmarks_aiger.tar.gz).
"""
import csv, collections, sys


def family(bench):
    return "/".join(bench.split("/")[:3])


def main(argv):
    csv_path, result, lo, hi, per_fam, count = argv[1:7]
    lo, hi, per_fam, count = float(lo), float(hi), int(per_fam), int(count)
    only = None
    if "--only" in argv:
        pf = argv[argv.index("--only") + 1]
        only = {ln.strip().replace("aiger/", "", 1)
                for ln in open(pf) if ln.strip().endswith(".aig")}

    best = collections.defaultdict(lambda: (float("inf"), None))
    for r in csv.DictReader(open(csv_path)):
        if r["result"] in ("sat", "unsat"):
            try:
                t = float(r["time_cpu"])
            except ValueError:
                continue
            if t < best[r["benchmark"]][0]:
                best[r["benchmark"]] = (t, r["result"])

    cands = []
    for bench, (t, res) in best.items():
        if res == result and lo <= t <= hi and (only is None or bench in only):
            cands.append((t, bench))
    cands.sort()

    seen = collections.Counter()
    picked = []
    for t, bench in cands:
        if seen[family(bench)] < per_fam:
            seen[family(bench)] += 1
            picked.append(bench)
        if len(picked) >= count:
            break

    for b in picked:
        print(b)


if __name__ == "__main__":
    main(sys.argv)

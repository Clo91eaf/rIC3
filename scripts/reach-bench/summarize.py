#!/usr/bin/env python3
"""Summarize shard.py result directories: solved counts, PAR-2, per-case times
and IC3 internals parsed from the solver logs.

usage: summarize.py TIME_LIMIT RESULT_DIR... [--cases LIST] [--json OUT] [--per-case]
"""
import argparse, csv, json, re
from collections import defaultdict
from pathlib import Path

KV = re.compile(r"^\s+(\w+): (\d+),?$")
SR = re.compile(r"^\s+(\w+): success: (\d+), fail: (\d+),")
STATS = ["num_solve", "num_mic", "num_down_sat", "push_fail", "propagate_push_fail", "propagate_push_succ",
         "cache_max_size", "cache_lookups", "cache_hits", "cache_scanned", "mic_reject", "core_refine",
         "exact_violation", "push_skip", "inf_push_skip", "may_created", "may_steps", "may_blocked",
         "may_reached_init", "may_closed_by_cache", "witness_queries", "witness_fail", "witness_states",
         "sim_states"]


def parse_log(folder):
    st = defaultdict(int)
    for name in ("stdout.log", "stderr.log"):
        p = Path(folder) / name
        if not p.exists():
            continue
        for line in p.read_text(errors="replace").splitlines():
            m = SR.match(line)
            if m:
                st[m[1] + "_succ"] += int(m[2]); st[m[1] + "_fail"] += int(m[3]); continue
            m = KV.match(line)
            if m:
                st[m[1]] += int(m[2])
    return st


def load(dirs):
    rows = {}
    for d in dirs:
        for f in Path(d).rglob("results.csv"):
            for r in csv.DictReader(open(f)):
                r["wall_s"] = float(r["wall_s"])
                r["stats"] = parse_log(r["result_dir"])
                rows[(r["solver"], r["benchmark"])] = r
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tl", type=float)
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--cases")
    ap.add_argument("--json")
    ap.add_argument("--per-case", action="store_true")
    a = ap.parse_args()
    rows = load(a.dirs)
    solvers = sorted({s for s, _ in rows}, key=lambda s: (s != "base", s))
    cases = sorted({b for _, b in rows})
    if a.cases:
        cases = [c.strip() for c in open(a.cases) if c.strip()]
    ok = lambda r: r is not None and r["status"] in ("SAT", "UNSAT") and r["wall_s"] <= a.tl
    out = {}
    print(f"{'solver':22} {'solved':>6} {'safe':>5} {'unsafe':>6} {'PAR2':>9} {'err':>4} {'missing':>7}")
    for s in solvers:
        rs = [rows.get((s, c)) for c in cases]
        solved = [r for r in rs if ok(r)]
        par2 = (sum(r["wall_s"] for r in solved) + 2 * a.tl * (len(cases) - len(solved))) / len(cases)
        err = sum(1 for r in rs if r is not None and r["status"] == "ERROR")
        miss = sum(1 for r in rs if r is None)
        safe = sum(1 for r in solved if r["status"] == "UNSAT")
        out[s] = dict(solved=len(solved), safe=safe, unsafe=len(solved) - safe, par2=par2, err=err, missing=miss)
        print(f"{s:22} {len(solved):6} {safe:5} {len(solved)-safe:6} {par2:9.1f} {err:4} {miss:7}")
    # contradictions
    for c in cases:
        ans = {rows[(s, c)]["status"] for s in solvers if (s, c) in rows and rows[(s, c)]["status"] in ("SAT", "UNSAT")}
        if len(ans) > 1:
            print("CONTRADICTION", c, {s: rows[(s, c)]["status"] for s in solvers if (s, c) in rows})
    # wins / losses versus base
    if "base" in solvers:
        print("\nvs base: only-solved-by / lost / faster(>1.2x, both>1s) / slower")
        for s in solvers[1:]:
            gain = [c for c in cases if ok(rows.get((s, c))) and not ok(rows.get(("base", c)))]
            lost = [c for c in cases if not ok(rows.get((s, c))) and ok(rows.get(("base", c)))]
            both = [c for c in cases if ok(rows.get((s, c))) and ok(rows.get(("base", c)))]
            fast = [c for c in both if max(rows[("base", c)]["wall_s"], rows[(s, c)]["wall_s"]) > 1 and rows[("base", c)]["wall_s"] > 1.2 * rows[(s, c)]["wall_s"]]
            slow = [c for c in both if max(rows[("base", c)]["wall_s"], rows[(s, c)]["wall_s"]) > 1 and rows[(s, c)]["wall_s"] > 1.2 * rows[("base", c)]["wall_s"]]
            tb = sum(rows[("base", c)]["wall_s"] for c in both); ts = sum(rows[(s, c)]["wall_s"] for c in both)
            print(f"  {s:22} +{len(gain)} -{len(lost)} faster {len(fast)} slower {len(slow)}; common {len(both)}: {tb:.1f}s vs {ts:.1f}s")
            for c in gain: print(f"      gained {c} ({rows[(s, c)]['wall_s']:.1f}s)")
            for c in lost: print(f"      lost   {c} (base {rows[('base', c)]['wall_s']:.1f}s)")
            out[s].update(gain=gain, lost=lost, faster=len(fast), slower=len(slow))
    print("\ninternals (sum over all cases):")
    print(f"{'solver':22} " + " ".join(f"{k[:11]:>11}" for k in STATS))
    for s in solvers:
        tot = defaultdict(int)
        for c in cases:
            r = rows.get((s, c))
            if r:
                for k, v in r["stats"].items(): tot[k] += v
        out[s]["internals"] = {k: tot[k] for k in STATS}
        print(f"{s:22} " + " ".join(f"{tot[k]:11}" for k in STATS))
    if a.per_case:
        print("\nper case wall_s (status):")
        print("case;" + ";".join(solvers))
        for c in cases:
            cells = []
            for s in solvers:
                r = rows.get((s, c))
                cells.append("-" if r is None else f"{r['wall_s']:.1f}{'' if ok(r) else '*'}{'S' if r['status']=='SAT' else ''}")
            print(Path(c).name + ";" + ";".join(cells))
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()

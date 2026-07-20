#!/usr/bin/env python3
"""Summarize a run_ab.sh results CSV: cases solved per condition, flips, speedups.

Usage: summarize.py <results.csv> [more.csv ...]   (rows are merged by benchmark)
"""
import csv, collections, sys

SOLVED = ("SAT", "UNSAT")


def main(paths):
    d = collections.defaultdict(dict)
    for p in paths:
        for r in csv.DictReader(open(p)):
            d[r["benchmark"]][r["cond"]] = (r["result"], r["wall_s"])

    base = share = 0
    wins, loses, faster, slower = [], [], 0, 0
    tb = ts = 0.0
    for b, cc in sorted(d.items()):
        if "baseline" not in cc or "share" not in cc:
            continue
        bR, bT = cc["baseline"]
        sR, sT = cc["share"]
        bok, sok = bR in SOLVED, sR in SOLVED
        base += bok
        share += sok
        if sok and not bok:
            wins.append(b)
        if bok and not sok:
            loses.append(b)
        if bok and sok:
            fb, fs = float(bT), float(sT)
            tb += fb
            ts += fs
            if fb > 2 and fs < fb * 0.7:
                faster += 1
            elif fs > 2 and fs > fb * 1.4:
                slower += 1

    n = sum(1 for cc in d.values() if "baseline" in cc and "share" in cc)
    print(f"cases:            {n}")
    print(f"baseline solved:  {base}")
    print(f"share solved:     {share}   (net {share - base:+d})")
    print(f"share-only wins:  {[b.split('/')[-1] for b in wins] or 'none'}")
    print(f"regressions:      {[b.split('/')[-1] for b in loses] or 'none'}")
    print(f"both-solved:      faster>30% {faster}, slower>40% {slower}")
    if tb:
        print(f"wall (both):      baseline {tb:.0f}s  share {ts:.0f}s  ({100*(ts-tb)/tb:+.0f}%)")


if __name__ == "__main__":
    main(sys.argv[1:] or ["ab_results.csv"])

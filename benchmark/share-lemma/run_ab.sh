#!/usr/bin/env bash
#
# A/B harness for portfolio lemma sharing.
#
# For every benchmark in a list file, runs the ic3_seeds portfolio twice —
# once WITHOUT sharing (baseline) and once WITH `--share-lemma` — under a wall
# timeout, and records result + wall time to a CSV. Compare the two `cond`
# columns to see cases solved and speedups.
#
# Usage:
#   run_ab.sh <list-file> <models-dir> <timeout-seconds> <out.csv>
#
# <models-dir> is the directory holding the HWMCC aiger files (see README for
# how to fetch them); benchmarks are located by basename beneath it.
#
# Note: `--share-lemma` here means the full sharing stack (finite-frame short
# lemmas + inductive invariants). Set RIC3_SHARE_FINITE_MAXLEN=0 in the env to
# restrict it to inductive invariants only (the "import-only" configuration).
set -u
LIST="${1:?list file}"; MDIR="${2:?models dir}"; TO="${3:-60}"; OUT="${4:-ab_results.csv}"
BIN="${RIC3_BIN:-$(git rev-parse --show-toplevel 2>/dev/null)/target/release/ric3}"

[ -x "$BIN" ] || { echo "ric3 binary not found at $BIN (build --release, or set RIC3_BIN)"; exit 2; }

echo "benchmark,cond,result,wall_s" > "$OUT"
run() { # $1 file  $2 cond  $3 flag(may be empty)
  local f="$1" cond="$2" flag="$3" start end res rc wall
  start=$(date +%s.%N)
  timeout "$TO" "$BIN" check "$f" portfolio --config ic3_seeds $flag > /tmp/_ab_run.txt 2>/dev/null
  rc=$?; end=$(date +%s.%N)
  if [ "$rc" -eq 124 ]; then
    res="TIMEOUT"
  else
    res=$(grep -iE "^SAT|^UNSAT|^Unknown" /tmp/_ab_run.txt | tail -1); res="${res:-NORES}"
  fi
  wall=$(awk "BEGIN{printf \"%.1f\", $end-$start}")
  echo "$(basename "$f"),$cond,$res,$wall" | tee -a "$OUT"
  pkill -9 -f "ric3 check" 2>/dev/null; sleep 0.5
}

while IFS= read -r rel; do
  [ -z "$rel" ] && continue
  f=$(find "$MDIR" -name "$(basename "$rel")" | head -1)
  [ -z "$f" ] && { echo "$(basename "$rel"),MISSING,,"; continue; }
  echo "### $(basename "$f")"
  run "$f" baseline ""
  run "$f" share "--share-lemma"
done < "$LIST"
echo "=== done -> $OUT ==="

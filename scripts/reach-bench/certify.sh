#!/usr/bin/env bash
# usage: certify.sh RIC3 TIMEOUT CASELIST -- IC3-FLAGS...
# Runs rIC3 with certificate export on each case and checks the certificate
# (safe: witness circuit, unsafe: trace) with certifaiger's `check`.
ric3=$1; tl=$2; list=$3; shift 4
CHECK=${CHECK:-/root/yjh-workspace/tools/certifaiger/bin/check}
BASE=/root/yjh-workspace/solver-benchmark/benchmark/HWMCC25
tmp=$(mktemp -d)
while read -r c; do
  [ -z "$c" ] && continue
  m=$BASE/$c
  res=$(timeout -s INT -k 10 "$tl" "$ric3" check "$m" --ui false --cert "$tmp/cert" ic3 "$@" 2>/dev/null </dev/null | grep -E '^(SAT|UNSAT|UNKNOWN)$' | tail -1)
  if [ "$res" = SAT ] || [ "$res" = UNSAT ]; then
    if timeout 1200 "$CHECK" "$m" "$tmp/cert" > "$tmp/log" 2>&1 </dev/null; then v=VALID
    elif [ "$res" = SAT ] && grep -q "expected '0' or '1'" "$tmp/log"; then
      # rIC3 prints don't-care bits as 'x', which aigsim rejects; retry with x -> 0.
      sed '1!s/x/0/g' "$tmp/cert" > "$tmp/cert0"
      if timeout 1200 "$CHECK" "$m" "$tmp/cert0" > "$tmp/log" 2>&1 </dev/null; then v=VALID-x0; else v=INVALID; fi
    else v=INVALID; fi
  else v=-; fi
  echo "$res $v $c"
  [ "$v" = INVALID ] && cp "$tmp/log" "${CERTLOG:-/tmp}/certfail-$(basename "$c").log"
  rm -f "$tmp/cert"
done < "$list"
rm -rf "$tmp"

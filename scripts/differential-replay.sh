#!/usr/bin/env bash
# Differential replay of lean4lean against the C++ kernel (`lake exe lean4lean --differential`).
#
# 1. `--fresh --exact --differential Init`: every safe, non-partial constant of `Init` and of
#    all its imports (every `Init.*` module) is replayed from the empty environment; each
#    declaration is checked by lean4lean and by the C++ kernel on lean4lean's environment.
# 2. `--exact --differential M` for each module `M` of `Lean4Lean.Tests`: the module's own
#    constants, replayed into the environment of its (trusted) imports. One process per module,
#    since each one imports `Lean` and the driver's per-module tasks are unbounded.
#
# Prints the per-run counts and their totals, and exits non-zero if any run fails, i.e. on any
# lean4lean-only rejection, kernel-only rejection or constructed-term mismatch, or any other
# replay error. Requires `lake build lean4lean Lean4Lean.Tests`.
set -uo pipefail
cd "$(dirname "$0")/.."

log=$(mktemp)
trap 'rm -f "$log"' EXIT
status=0

run() {
  echo "+ lake exe lean4lean $*"
  local out rc
  out=$(lake exe lean4lean "$@" 2>&1)
  rc=$?
  printf '%s\n' "$out" >> "$log"
  printf '%s\n' "$out" | grep -E '^differential|rejection|mismatch' || true
  if [ "$rc" -ne 0 ]; then
    status=1
    echo "FAILED (exit $rc):"
    printf '%s\n' "$out" | tail -20
  fi
}

run --fresh --exact --differential Init

for f in Lean4Lean/Tests/*.lean; do
  m=$(echo "${f%.lean}" | tr / .)
  run --exact --differential "$m"
done

awk '/^differential [^:]*: [0-9]+ declarations checked/ {
       sub(/^differential [^:]*: /, "")
       n = split($0, parts, ", ")
       for (i = 1; i <= n; i++) { split(parts[i], w, " "); total[i] += w[1]; label[i] = substr(parts[i], length(w[1]) + 2) }
       runs++
     }
     END {
       printf "differential total over %d runs:", runs
       for (i = 1; i in total; i++) printf "%s %d %s", (i > 1 ? "," : ""), total[i], label[i]
       printf "\n"
     }' "$log"

if [ "$status" -ne 0 ]; then
  echo "differential replay FAILED" >&2
fi
exit "$status"

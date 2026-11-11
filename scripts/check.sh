#!/bin/sh
# Local reviewer checks. Run after `lake exe cache get`.
set -eu
cd "$(dirname "$0")/.."
check_log=$(mktemp "${TMPDIR:-/tmp}/wolfesimplex-check.XXXXXX")
trap 'rm -f "$check_log"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

run_check() {
  check_label=$1
  shift
  printf '%s ... ' "$check_label"
  if "$@" >"$check_log" 2>&1; then
    printf 'passed\n'
  else
    check_status=$?
    printf 'FAILED\n' >&2
    cat "$check_log" >&2
    exit "$check_status"
  fi
}

run_check '[1/13] Library build' lake build
run_check '[2/13] Project axiom audit' lake env lean scripts/CheckAxioms.lean
run_check '[3/13] Paper path and statement boundary' lake env lean scripts/CheckPaperPath.lean
run_check '[4/13] Executable construction example' lake env lean scripts/CheckConstruction.lean
run_check '[5/13] Trace projection fixture' lake env lean scripts/CheckEfficiency.lean

run_check '[6/13] Primitive execution examples' lake env lean scripts/CheckExecution.lean

run_check '[7/13] Run-local nondegeneracy regression' lake env lean scripts/CheckRunLocal.lean
run_check '[8/13] Capacity-slack and bound-flip regressions' lake env lean scripts/CheckNetworkFlow.lean
run_check '[9/13] Native incidence and forest regressions' lake env lean scripts/CheckNetworkIncidence.lean
run_check '[10/13] Corollary 4 rational count and query regressions' lake env lean scripts/CheckCorollary4.lean
run_check '[11/13] Executed native network preprocessing' lake env lean scripts/CheckNetworkPreparation.lean
run_check '[12/13] Quantitative Table 1 and rational source regression' lake env lean scripts/CheckTable1.lean
run_check '[13/13] Infinite-capacity normalization and exact count regression' lake env lean scripts/CheckInfiniteCapacity.lean

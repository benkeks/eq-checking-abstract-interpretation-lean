#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
lake build Main
binary=.lake/build/bin/Main

check_output() {
  local expected=$1
  shift
  local actual
  actual=$("$binary" "$@" 2>&1)
  if [[ "$actual" != "$expected" ]]; then
    printf 'Expected: %s\nActual:   %s\n' "$expected" "$actual" >&2
    exit 1
  fi
}

check_output 'tracePreordered(5, 15) = true' trace assets/peterson_mutex_5_15.csv 5 15
check_output 'tracePreordered(15, 2) = false' trace assets/peterson_mutex_5_15.csv 15 2
check_output 'Holding preorders for (0, 0): trace, simulation, failures, ready simulation' \
  ready tests/ready_modes.csv 0 0
check_output 'Holding preorders for (0, 1): trace, simulation' ready tests/ready_modes.csv 0 1
check_output 'Holding preorders for (4, 5): trace, failures' ready tests/ready_modes.csv 4 5
check_output 'Holding preorders for (1, 0): none' ready tests/ready_modes.csv 1 0
check_output "Input error: unknown mode 'unknown' (expected trace or ready)" \
  unknown tests/ready_modes.csv 0 1
check_output 'Usage: Main <trace|ready> <transitions.csv> <left-state-id> <right-state-id>' \
  tests/ready_modes.csv 0 1

bad_csv=$(mktemp)
trap 'rm -f "$bad_csv"' EXIT
printf '5,15\n' > "$bad_csv"
check_output 'CSV parse error: line 1: expected exactly three comma-separated fields' \
  ready "$bad_csv" 5 15

printf 'Executable interface tests passed\n'
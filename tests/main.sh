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

check_output 'tracePreordered(5, 15) = true' assets/peterson_mutex_5_15.csv 5 15
check_output 'tracePreordered(15, 2) = false' assets/peterson_mutex_5_15.csv 15 2

bad_csv=$(mktemp)
trap 'rm -f "$bad_csv"' EXIT
printf '5,15\n' > "$bad_csv"
check_output 'CSV parse error: line 1: expected exactly three comma-separated fields' \
  "$bad_csv" 5 15

printf 'Executable interface tests passed\n'
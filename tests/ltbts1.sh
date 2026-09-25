#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
lake build Main
binary=.lake/build/bin/Main
report=tests/ltbts1.results
printf 'left,right,seconds,preorders,status\n' > "$report"

pairs=(
  'L13 R13'
  'L16 R16'
  'L21 R21'
  'L24 R24'
  'L27 R27'
  'L31 R31'
  'L34 R31'
  'L38 R24'
  'L42 R42'
  'L50 R50'
)

run_pair() {
  local left=$1 right=$2 output exit_code elapsed_ms preorders status
  local start end
  start=$(date +%s%N)
  if output=$(timeout 30s "$binary" ready assets/ltbts1.csv "$left" "$right" 2>&1); then
    exit_code=0
  else
    exit_code=$?
  fi
  end=$(date +%s%N)
  elapsed_ms=$(((end - start) / 1000000))

  preorders=
  if ((exit_code == 124)); then
    status=timeout
  elif ((exit_code != 0)); then
    status=error
    printf '%s -> %s: %s\n' "$left" "$right" "$output" >&2
  elif [[ "$output" == "Holding preorders for ($left, $right): "* ]]; then
    status=ok
    preorders=${output#"Holding preorders for ($left, $right): "}
  else
    status=error
    printf '%s -> %s: unexpected output: %s\n' "$left" "$right" "$output" >&2
  fi

  printf '%s,%s,%d.%03d,"%s",%s\n' "$left" "$right" \
    "$((elapsed_ms / 1000))" "$((elapsed_ms % 1000))" "$preorders" "$status" >> "$report"
}

for pair in "${pairs[@]}"; do
  read -r left right <<< "$pair"
  run_pair "$left" "$right"
  run_pair "$right" "$left"
done

printf 'Wrote %s\n' "$report"
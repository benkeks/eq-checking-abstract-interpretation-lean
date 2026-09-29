#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
lake build Main
binary=.lake/build/bin/Main
report=${REPORT:-tests/ltbts1.results}
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

declare -A times preorders_for statuses
examples=()
for pair in "${pairs[@]}"; do
  read -r left right <<< "$pair"
  examples+=("$left $right" "$right $left")
done

run_pair() {
  local left=$1 right=$2 output exit_code elapsed_ms preorders status key
  local start end
  start=$(date +%s%N)
  if output=$(timeout 30s "$binary" ready assets/ltbts1.csv "$left" "$right" --finest 2>&1); then
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
  elif [[ "$output" == "Finest preorders for ($left, $right): "* ]]; then
    status=ok
    preorders=${output#"Finest preorders for ($left, $right): "}
  else
    status=error
    printf '%s -> %s: unexpected output: %s\n' "$left" "$right" "$output" >&2
  fi

  key="$left $right"
  times[$key]="${times[$key]-}$elapsed_ms "
  if [[ "$status" == ok ]]; then
    if [[ -n "${preorders_for[$key]-}" && "${preorders_for[$key]}" != "$preorders" ]]; then
      statuses[$key]=error
      printf '%s -> %s: inconsistent preorders: %s vs %s\n' \
        "$left" "$right" "${preorders_for[$key]}" "$preorders" >&2
    else
      preorders_for[$key]=$preorders
    fi
  elif [[ "$status" == error || "${statuses[$key]-}" != error ]]; then
    statuses[$key]=$status
  fi
}

for round in {1..5}; do
  mapfile -t shuffled < <(printf '%s\n' "${examples[@]}" | shuf)
  for pair in "${shuffled[@]}"; do
    read -r left right <<< "$pair"
    run_pair "$left" "$right"
  done
done

for pair in "${examples[@]}"; do
  read -r left right <<< "$pair"
  read -r -a samples <<< "${times[$pair]}"
  mapfile -t sorted < <(printf '%s\n' "${samples[@]}" | sort -n)
  median_ms=${sorted[2]}
  printf '%s,%s,%d.%03d,"%s",%s\n' "$left" "$right" \
    "$((median_ms / 1000))" "$((median_ms % 1000))" \
    "${preorders_for[$pair]-}" "${statuses[$pair]-ok}" >> "$report"
done

printf 'Wrote %s\n' "$report"
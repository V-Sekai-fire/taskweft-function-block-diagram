#!/usr/bin/env bash
# The Godot half of the scan gate, on a desk with a Godot 4.5 binary: every
# generated harness x every trace, the guest's outputs must equal the Lean
# reference's; then the negative control must mismatch; then the latency rows.
#
#   TASKWEFT_GODOT=/path/to/godot scripts/diff_scan.sh [outdir]
#
# Exit 1 on the first mismatch, on a negative control that matches, or on a
# latency row over its rail. Writes bench/tick_latency.csv.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"
B="$HERE/.lake/build/bin/taskweft_fbd_compiler"
[ -x "$B" ] || B="$B.exe"
OUT="${1:-$HERE/work/gen}"
mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd)"
PROJECT="${TASKWEFT_SANDBOX_PROJECT:-$HERE/../taskweft-godot-sandbox/priv/godot_project}"
GODOT="${TASKWEFT_GODOT:?set TASKWEFT_GODOT to a Godot 4.5 binary}"
FLOOR_P99_US=200
LARGEST_P99_US=1000

winpath() { if command -v cygpath >/dev/null 2>&1; then cygpath -w "$1"; else echo "$1"; fi; }

run_godot() {
  MSYS_NO_PATHCONV=1 timeout 300 "$GODOT" --headless --path "$(winpath "$PROJECT")" \
    --script res://scripts/scan_runner.gd -- "$@" 2>&1 | grep -v '^$\|Godot Engine'
}

mkdir -p "$OUT" "$PROJECT/plans/gen" "$HERE/bench"
"$B" gen-scan "$OUT" || exit 1

pairs=0; mismatches=0; faults=0
for fbd in "$OUT"/*.fbd; do
  name="$(basename "$fbd" .fbd)"
  "$B" emit-scan "$fbd" "$PROJECT/plans/gen/$name.sgd" >/dev/null || { echo "emit-scan refused $name"; exit 1; }
  for trace in "$OUT"/trace_*.json; do
    tname="$(basename "$trace" .json)"
    expect="$OUT/$name.$tname.expected.jsonl"
    "$B" sim "$fbd" "$trace" > "$expect" || { echo "sim refused $name on $tname"; exit 1; }
    grep -q '"fault"' "$expect" && faults=$((faults + 1))
    pairs=$((pairs + 1))
    result="$(run_godot --guest "res://plans/gen/$name.sgd" --trace "$(winpath "$trace")" --expect "$(winpath "$expect")")"
    if ! grep -q '^match:' <<<"$result"; then
      echo "MISMATCH $name on $tname:"; echo "$result" | head -5
      mismatches=$((mismatches + 1))
      exit 1
    fi
  done
done
echo "differential: $pairs pair(s) matched, $faults with a fault line, 0 mismatches"

F="$HERE/fixtures/scan"
cp "$F/negative/ton_off_by_one.sgd" "$PROJECT/plans/ton_off_by_one.sgd"
neg="$(run_godot --guest res://plans/ton_off_by_one.sgd --trace "$(winpath "$F/walk_trace.json")" --expect "$(winpath "$F/walk_expected.jsonl")")"
if grep -q '^match:' <<<"$neg"; then
  echo "the negative control matched; the differential test is decoration"; exit 1
fi
echo "negative control: $(echo "$neg" | head -1)"

bench_row() {
  local name="$1" fbd="$2" trace="$3"
  "$B" emit-scan "$fbd" "$PROJECT/plans/$name.sgd" >/dev/null || exit 1
  local blocks; blocks="$("$B" check "$fbd" | sed -n 's/.*controller, \([0-9]*\) block.*/\1/p')"
  local row; row="$(run_godot --guest "res://plans/$name.sgd" --trace "$(winpath "$trace")" --bench 10000 | sed -n '/^[0-9]/p' | head -1)"
  echo "$name,$blocks,$row"
}
largest="$(ls -S "$OUT"/*.fbd | head -1)"
csv="$HERE/bench/tick_latency.csv"
echo "controller,blocks,p50_us,p99_us,max_us" > "$csv"
bench_row floor_move "$F/floor_move.fbd" "$F/walk_trace.json" >> "$csv"
bench_row walk_ctl "$F/walk_ctl.fbd" "$F/walk_trace.json" >> "$csv"
bench_row "$(basename "$largest" .fbd)" "$largest" "$OUT/trace_step_60.json" >> "$csv"
cat "$csv"
floor_p99="$(sed -n '2p' "$csv" | cut -d, -f4)"
walk_p99="$(sed -n '3p' "$csv" | cut -d, -f4)"
[ "${floor_p99:-9999}" -lt "$FLOOR_P99_US" ] || { echo "floor p99 ${floor_p99}us over the ${FLOOR_P99_US}us rail"; exit 1; }
[ "${walk_p99:-9999}" -lt "$LARGEST_P99_US" ] || { echo "walk_ctl p99 ${walk_p99}us over the ${LARGEST_P99_US}us rail"; exit 1; }
echo "latency rails hold"

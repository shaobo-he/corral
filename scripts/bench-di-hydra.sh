#!/usr/bin/env bash
# Benchmark SI vs SI+DI vs sequential HYDRA (+ optional experimental multicore).
# Usage: scripts/bench-di-hydra.sh [bpl files...]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CORRAL="${CORRAL:-$ROOT/source/Corral/bin/Release/net8.0/corral}"
Z3DIR="${Z3DIR:-/mnt/local/smack-deps/z3/bin}"
export PATH="${Z3DIR}:$PATH"
export DOTNET_ROOT="${DOTNET_ROOT:-/home/shaobo/.dotnet}"

if [[ ! -x "$CORRAL" ]]; then
  echo "Building corral..."
  dotnet build -c Release "$ROOT/source/Corral.sln"
fi

FILES=("$@")
if [[ ${#FILES[@]} -eq 0 ]]; then
  FILES=(
    "$ROOT/test/regression/hydra/bug_reach.bpl"
    "$ROOT/test/regression/hydra/bug_avoid.bpl"
    "$ROOT/test/regression/hydra/both_safe.bpl"
    "$ROOT/test/regression/hydra/nested.bpl"
    "$ROOT/test/regression/hydra/rec.bpl"
    "$ROOT/test/regression/smack/a.bpl"
  )
fi

MODES=(
  "si:"
  "di:/di"
  "hydra:/hydra /set:HydraStats"
  "hydra2:/hydraWorkers:2 /set:HydraStats"
)

printf '%-20s %-8s %10s %12s %s\n' "bench" "mode" "wall_s" "verdict" "extra"
for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || continue
  base=$(basename "$f" .bpl)
  for spec in "${MODES[@]}"; do
    name="${spec%%:*}"
    flags="${spec#*:}"
    # shellcheck disable=SC2086
    out=$(timeout 300 "$CORRAL" "$f" /main:main /recursionBound:3 $flags 2>&1 || true)
    wall=$(echo "$out" | sed -n 's/^Total Time: \([0-9.]*\).*/\1/p' | head -1)
    [[ -z "$wall" ]] && wall="?"
    if echo "$out" | grep -q 'Program has no bugs'; then
      verdict="SAFE"
    elif echo "$out" | grep -q 'True bug'; then
      verdict="UNSAFE"
    elif echo "$out" | grep -q 'internal bug\|Prover error'; then
      verdict="ERROR"
    else
      verdict="OTHER"
    fi
    extra=$(echo "$out" | grep -E 'HYDRA sequential:|HYDRA multicore stats:|Time spent inside DI:' | head -1 | tr -s ' ')
    printf '%-20s %-8s %10s %12s %s\n' "$base" "$name" "$wall" "$verdict" "$extra"
  done
done

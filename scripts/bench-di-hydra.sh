#!/usr/bin/env bash
# Benchmark SI, SI+DI, and HYDRA+DI at 1/2/4/8 local workers.
# Usage: scripts/bench-di-hydra.sh [bpl files...]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CORRAL="${CORRAL:-$ROOT/source/Corral/bin/Release/net8.0/corral}"
Z3DIR="${Z3DIR:-/mnt/local/smack-deps/z3/bin}"
export PATH="${Z3DIR}:$PATH"
export DOTNET_ROOT="${DOTNET_ROOT:-/home/shaobo/.dotnet}"
DOTNET="${DOTNET:-$DOTNET_ROOT/dotnet}"

SKIP_BUILD="${SKIP_BUILD:-0}"
BENCH_TIMEOUT="${BENCH_TIMEOUT:-600}"
BENCH_KILL_AFTER="${BENCH_KILL_AFTER:-30}"
BENCH_RECURSION_BOUND="${BENCH_RECURSION_BOUND:-3}"
BENCH_REPEATS="${BENCH_REPEATS:-1}"
SMACK_TEST_ROOT="${SMACK_TEST_ROOT:-/home/shaobo/smack-project/smack/test}"

if [[ "$SKIP_BUILD" != "0" && "$SKIP_BUILD" != "1" ]]; then
  echo "SKIP_BUILD must be 0 or 1" >&2
  exit 2
fi
if [[ ! "$BENCH_RECURSION_BOUND" =~ ^[0-9]+$ ]]; then
  echo "BENCH_RECURSION_BOUND must be a non-negative integer" >&2
  exit 2
fi
if [[ ! "$BENCH_REPEATS" =~ ^[1-9][0-9]*$ ]]; then
  echo "BENCH_REPEATS must be a positive integer" >&2
  exit 2
fi

declare -a FILES=()
declare -A EXPECTED_VERDICTS=()
if [[ $# -eq 0 ]]; then
  NTDRIVER_NAMES=(
    cdaudio_simpl1_true.cil-no-reuse-impls-corral.bpl
    cdaudio_simpl1_false.cil-no-reuse-impls-corral.bpl
    diskperf_simpl1_true.cil-no-reuse-impls-corral.bpl
    diskperf_false.i.cil-no-reuse-impls-corral.bpl
    floppy_simpl4_true.cil-no-reuse-impls-corral.bpl
    floppy_simpl4_false.cil-no-reuse-impls-corral.bpl
    kbfiltr_simpl2_true.cil-no-reuse-impls-corral.bpl
    kbfiltr_simpl2_false.cil-no-reuse-impls-corral.bpl
    parport_true.i.cil-no-reuse-impls-corral.bpl
    parport_false.i.cil-no-reuse-impls-corral.bpl
  )
  NTDRIVER_EXPECTED=(
    SAFE UNSAFE SAFE UNSAFE SAFE UNSAFE SAFE UNSAFE SAFE UNSAFE
  )
  missing=()
  for i in "${!NTDRIVER_NAMES[@]}"; do
    path="$SMACK_TEST_ROOT/${NTDRIVER_NAMES[$i]}"
    if [[ -f "$path" ]]; then
      FILES+=("$path")
      EXPECTED_VERDICTS["$path"]="${NTDRIVER_EXPECTED[$i]}"
    else
      missing+=("$path")
    fi
  done
  if [[ ${#missing[@]} -ne 0 ]]; then
    echo "Missing required default ntdriver corpus files:" >&2
    printf '  %s\n' "${missing[@]}" >&2
    exit 2
  fi
else
  FILES=("$@")
fi

missing=()
for path in "${FILES[@]}"; do
  [[ -f "$path" ]] || missing+=("$path")
done
if [[ ${#missing[@]} -ne 0 ]]; then
  echo "Missing benchmark input files:" >&2
  printf '  %s\n' "${missing[@]}" >&2
  exit 2
fi

if [[ -z "${BENCH_RESULTS_DIR:-}" ]]; then
  BENCH_RESULTS_DIR="$(mktemp -d /tmp/corral-di-hydra-bench.XXXXXX)"
else
  mkdir -p "$BENCH_RESULTS_DIR"
fi
RUN_TAG="$(date -u +%Y%m%dT%H%M%SZ)-$$"
BUILD_LOG="$BENCH_RESULTS_DIR/build-$RUN_TAG.log"
METADATA_FILE="$BENCH_RESULTS_DIR/metadata-$RUN_TAG.txt"
SUMMARY_FILE="$BENCH_RESULTS_DIR/summary-$RUN_TAG.tsv"

if [[ "$SKIP_BUILD" == "0" ]]; then
  echo "Building Corral Release (set SKIP_BUILD=1 to use an existing binary)..."
  set +e
  "$DOTNET" build -c Release "$ROOT/source/Corral.sln" 2>&1 | tee "$BUILD_LOG"
  build_status=${PIPESTATUS[0]}
  set -e
  if [[ $build_status -ne 0 ]]; then
    echo "Release build failed; see $BUILD_LOG" >&2
    exit "$build_status"
  fi
else
  printf 'Build skipped by SKIP_BUILD=1\n' >"$BUILD_LOG"
fi
if [[ ! -x "$CORRAL" ]]; then
  echo "Corral executable is missing or not executable: $CORRAL" >&2
  exit 2
fi

git_commit="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || true)"
dotnet_version="$("$DOTNET" --version 2>&1 || true)"
z3_path="$(command -v z3 || true)"
z3_version="$(z3 --version 2>&1 || true)"
corral_sha256="$(sha256sum "$CORRAL" 2>/dev/null | awk '{print $1}' || true)"
{
  printf 'run_tag=%s\n' "$RUN_TAG"
  printf 'started_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'root=%s\n' "$ROOT"
  printf 'git_commit=%s\n' "${git_commit:-unknown}"
  printf 'corral=%s\n' "$CORRAL"
  printf 'corral_sha256=%s\n' "${corral_sha256:-unknown}"
  printf 'dotnet=%s\n' "$DOTNET"
  printf 'dotnet_version=%s\n' "${dotnet_version:-unknown}"
  printf 'z3=%s\n' "${z3_path:-unknown}"
  printf 'z3_version=%s\n' "${z3_version:-unknown}"
  printf 'host=%s\n' "$(uname -a)"
  printf 'logical_cpus=%s\n' "$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf unknown)"
  printf 'skip_build=%s\n' "$SKIP_BUILD"
  printf 'timeout=%s\n' "$BENCH_TIMEOUT"
  printf 'kill_after=%s\n' "$BENCH_KILL_AFTER"
  printf 'recursion_bound=%s\n' "$BENCH_RECURSION_BOUND"
  printf 'repeats=%s\n' "$BENCH_REPEATS"
  printf 'smack_test_root=%s\n' "$SMACK_TEST_ROOT"
  printf 'git_status_begin\n'
  git -C "$ROOT" status --short 2>/dev/null || true
  printf 'git_status_end\n'
  for path in "${FILES[@]}"; do
    input_sha256="$(sha256sum "$path" 2>/dev/null | awk '{print $1}' || true)"
    printf 'input=%s\texpected=%s\tsha256=%s\n' \
      "$path" "${EXPECTED_VERDICTS["$path"]-}" "${input_sha256:-unknown}"
  done
} >"$METADATA_FILE"

MODE_NAMES=(si di hydra hydra2 hydra4 hydra8)
MODE_FLAGS=(
  "/set:BenchStats"
  "/di /set:BenchStats"
  "/hydra /set:HydraStats /set:BenchStats"
  "/hydraWorkers:2 /set:HydraStats /set:BenchStats"
  "/hydraWorkers:4 /set:HydraStats /set:BenchStats"
  "/hydraWorkers:8 /set:HydraStats /set:BenchStats"
)

aggregate_stats() {
  awk '
    function add_common(k, v) {
      if (k == "expansions") expansions += v
      else if (k == "freshVCs") fresh += v
      else if (k == "merges") merges += v
      else if (k == "rejectedMerges") rejected += v
      else if (k == "solverCalls") solverCalls += v
      else if (k == "smtMs") smtMs += v
    }
    /^BENCH stats:/ {
      commonRecords++
      for (i = 3; i <= NF; i++) {
        split($i, a, "=")
        add_common(a[1], a[2] + 0)
      }
    }
    /^HYDRA multicore stats:/ {
      commonRecords++
      hydraRecords++
      for (i = 4; i <= NF; i++) {
        split($i, a, "=")
        k = a[1]
        v = a[2]
        if (k == "expansions" || k == "freshVCs" || k == "merges" ||
            k == "rejectedMerges" || k == "solverCalls" || k == "smtMs") {
          add_common(k, v + 0)
        } else if (k == "partitions") {
          split(v, p, "/")
          partitionsSolved += p[1] + 0
          partitionsCreated += p[2] + 0
          sawCreated = 1
        } else if (k == "wall") {
          sub(/ms$/, "", v)
          hydraWallMs += v + 0
        } else if (k == "splits") hydraSplits += v + 0
        else if (k == "stolen") stolen += v + 0
        else if (k == "reconstructed") reconstructed += v + 0
        else if (k == "localReuse") localReuse += v + 0
        else if (k == "ownerDequeues") ownerDequeues += v + 0
        else if (k == "prefixEarlierGuards") prefixEarlierGuards += v + 0
        else if (k == "publishedSiblings") publishedSiblings += v + 0
        else if (k == "publicationDeclined") publicationDeclined += v + 0
        else if (k == "coordCloneMs") coordCloneMs += v + 0
        else if (k == "initLockWaitMs") initLockWaitMs += v + 0
        else if (k == "workerCloneMs") workerCloneMs += v + 0
        else if (k == "workerPrepareMs") workerPrepareMs += v + 0
        else if (k == "workerSiCtorMs") workerSiCtorMs += v + 0
        else if (k == "workerPreSearchMs") workerPreSearchMs += v + 0
        else if (k == "closeLockWaitMs") closeLockWaitMs += v + 0
        else if (k == "workerCloseMs") workerCloseMs += v + 0
        else if (k == "bound") bound += v + 0
        else if (k == "unknown") unknown += v + 0
        else if (k == "peakWorkers" && v + 0 > peakWorkers) peakWorkers = v + 0
        else if (k == "peakSolversApprox" && v + 0 > peakSolvers) peakSolvers = v + 0
      }
    }
    /^HYDRA sequential:/ {
      hydraRecords++
      for (i = 3; i <= NF; i++) {
        split($i, a, "=")
        k = a[1]
        v = a[2]
        if (k == "splits") hydraSplits += v + 0
        else if (k == "partitions") partitionsSolved += v + 0
        else if (k == "prefixEarlierGuards") prefixEarlierGuards += v + 0
        else if (k == "decisionTime") {
          sub(/s$/, "", v)
          decisionTimeS += v + 0
        }
      }
    }
    /^HYDRA witness stats:/ {
      witnessRecords++
      for (i = 4; i <= NF; i++) {
        split($i, a, "=")
        k = a[1]
        v = a[2] + 0
        if (k == "produced") witnessesProduced += v
        else if (k == "confirmations") witnessConfirmations += v
        else if (k == "failures") witnessFailures += v
        else if (k == "replaySteps") witnessReplaySteps += v
        else if (k == "decisions") witnessDecisions += v
      }
    }
    /^Time spent inside DI:/ {
      diRecords++
      diTimeS += $5 + 0
    }
    END {
      printf "statsRecords=%d expansions=%d freshVCs=%d merges=%d rejectedMerges=%d solverCalls=%d smtMs=%d", \
        commonRecords, expansions, fresh, merges, rejected, solverCalls, smtMs
      if (diRecords > 0) printf " diTimeS=%.2f", diTimeS
      if (hydraRecords > 0) {
        printf " hydraRecords=%d hydraSplits=%d partitionsSolved=%d", \
          hydraRecords, hydraSplits, partitionsSolved
        if (sawCreated) printf " partitionsCreated=%d", partitionsCreated
        printf " stolen=%d reconstructed=%d localReuse=%d ownerDequeues=%d prefixEarlierGuards=%d publishedSiblings=%d publicationDeclined=%d hydraWallMs=%d decisionTimeS=%.2f peakWorkers=%d peakSolversApprox=%d bound=%d unknown=%d", \
          stolen, reconstructed, localReuse, ownerDequeues, prefixEarlierGuards, \
          publishedSiblings, publicationDeclined, hydraWallMs, decisionTimeS, peakWorkers, peakSolvers, bound, unknown
        printf " coordCloneMs=%d initLockWaitMs=%d workerCloneMs=%d workerPrepareMs=%d workerSiCtorMs=%d workerPreSearchMs=%d closeLockWaitMs=%d workerCloseMs=%d", \
          coordCloneMs, initLockWaitMs, workerCloneMs, workerPrepareMs, workerSiCtorMs, \
          workerPreSearchMs, closeLockWaitMs, workerCloseMs
        if (witnessRecords > 0) {
          printf " witnessesProduced=%d witnessConfirmations=%d witnessFailures=%d witnessReplaySteps=%d witnessDecisions=%d", \
            witnessesProduced, witnessConfirmations, witnessFailures, witnessReplaySteps, witnessDecisions
        }
      }
    }
  ' "$1"
}

mismatch=0
file_index=0
printf 'bench\trepeat\tmode\twall_s\tpeak_rss_kb\tverdict\texpected\tstats\tlog\n' >"$SUMMARY_FILE"
printf 'Results: %s\n' "$BENCH_RESULTS_DIR"
printf 'Configuration: recursionBound=%s timeout=%s killAfter=%s repeats=%s\n' \
  "$BENCH_RECURSION_BOUND" "$BENCH_TIMEOUT" "$BENCH_KILL_AFTER" "$BENCH_REPEATS"
printf '%-42s %4s %-8s %10s %12s %10s %-8s %s\n' \
  "bench" "rep" "mode" "wall_s" "peak_rss_kb" "verdict" "expected" "stats"

for f in "${FILES[@]}"; do
  file_index=$((file_index + 1))
  base="$(basename "$f" .bpl)"
  safe_base="${base//[^[:alnum:]_.-]/_}"
  expected="${EXPECTED_VERDICTS["$f"]-}"
  [[ -n "$expected" ]] || expected="-"
  for ((repetition = 1; repetition <= BENCH_REPEATS; repetition++)); do
    baseline=""
    for mode_index in "${!MODE_NAMES[@]}"; do
      name="${MODE_NAMES[$mode_index]}"
      read -r -a flags <<<"${MODE_FLAGS[$mode_index]}"
      cmd=(
        "$CORRAL" "$f" /main:main
        "/recursionBound:$BENCH_RECURSION_BOUND"
        "${flags[@]}"
      )
      printf -v log_name '%02d-%s.r%02d.%s.%s.log' \
        "$file_index" "$safe_base" "$repetition" "$name" "$RUN_TAG"
      log_file="$BENCH_RESULTS_DIR/$log_name"
      command_file="${log_file%.log}.command"
      {
        printf '/usr/bin/time -f %q timeout --verbose --kill-after=%q %q' \
          '__BENCH_RESOURCE__ wall=%e maxrss_kb=%M' "$BENCH_KILL_AFTER" "$BENCH_TIMEOUT"
        printf ' %q' "${cmd[@]}"
        printf '\n'
      } >"$command_file"

      set +e
      /usr/bin/time -f '__BENCH_RESOURCE__ wall=%e maxrss_kb=%M' \
        timeout --verbose --kill-after="$BENCH_KILL_AFTER" "$BENCH_TIMEOUT" \
        "${cmd[@]}" >"$log_file" 2>&1
      status=$?
      set -e
      printf '%s\n' "$status" >"${log_file%.log}.status"

      wall="$(sed -n 's/^__BENCH_RESOURCE__ wall=\([^ ]*\).*/\1/p' "$log_file" | tail -1)"
      maxrss="$(sed -n 's/^__BENCH_RESOURCE__ .*maxrss_kb=\([0-9]*\).*/\1/p' "$log_file" | tail -1)"
      [[ -n "$wall" ]] || wall="?"
      [[ -n "$maxrss" ]] || maxrss="?"

      if [[ $status -eq 124 ]] || \
          { [[ $status -eq 137 ]] && grep -q '^timeout: sending signal KILL' "$log_file"; }; then
        verdict="TIMEOUT"
      elif [[ $status -ne 0 ]] || \
          grep -Eqi 'internal bug|ProverException|Prover error|out of (memory|resources)|unknown response' "$log_file"; then
        verdict="ERROR"
      elif grep -q 'True bug' "$log_file"; then
        verdict="UNSAFE"
      elif grep -Eq 'Reached recursion bound|Exhausted recursion bound' "$log_file"; then
        verdict="BOUND"
      elif grep -q 'Program has no bugs' "$log_file"; then
        verdict="SAFE"
      else
        verdict="OTHER"
      fi

      agreement=""
      if [[ "$verdict" != "SAFE" && "$verdict" != "UNSAFE" ]]; then
        mismatch=1
      fi
      if [[ "$name" == "si" ]]; then
        baseline="$verdict"
        if [[ "$expected" != "-" && "$verdict" != "$expected" ]]; then
          agreement="SOURCE_MISMATCH expected=$expected"
          mismatch=1
        fi
      elif [[ "$verdict" != "$baseline" ]]; then
        agreement="MISMATCH expected_si=$baseline"
        mismatch=1
      fi

      metrics="$(aggregate_stats "$log_file")"
      [[ -n "$agreement" ]] && metrics="$agreement; $metrics"
      printf '%-42s %4s %-8s %10s %12s %10s %-8s %s\n' \
        "$base" "$repetition" "$name" "$wall" "$maxrss" "$verdict" "$expected" "$metrics"
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$base" "$repetition" "$name" "$wall" "$maxrss" "$verdict" "$expected" \
        "$metrics" "$log_file" >>"$SUMMARY_FILE"
    done
  done
done

printf 'metadata=%s\nsummary=%s\n' "$METADATA_FILE" "$SUMMARY_FILE"
exit "$mismatch"

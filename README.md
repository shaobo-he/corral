# mini-corral

[![License][license-badge]](LICENSE.txt)
[![CI][ci-badge]][ci]

**mini-corral** is a trimmed-down [Corral](https://github.com/boogie-org/corral)
tailored for the [SMACK](https://github.com/smackers/smack) verification
toolchain. It keeps only the code paths that SMACK actually exercises (see
SMACK's `top.py` and `svcomp/utils.py`) and drops everything else.

> **Branch note.** This branch builds on `mini-corral-boogie-3.5.6-refresh`,
> restores the simplified `mini-corral` DAG-inlining implementation, and adds
> sequential plus local-multicore HYDRA partition search. It targets
> **Boogie 3.5.6 / .NET 8**.

Corral is a solver for the reachability modulo theories problem: given a Boogie
program, it looks for an execution that reaches an `assert` violation, using
stratified inlining over a bounded recursion depth plus variable-abstraction
refinement. Learn more about upstream Corral here:
http://research.microsoft.com/en-us/projects/verifierq

## What is different from upstream Corral

Relative to `boogie-org/corral` master, this branch removes about 45k lines
from `source/` (133 C# files down to 29). The verification behavior on SMACK's
invocations is unchanged — every removal was validated against a golden-output
harness (including SV-COMP mode) and the regression suite.

**Scope includes sequential SI, DAG inlining, and local multicore HYDRA.** `/k`
still parses, while the old distributed/server infrastructure remains removed.

Restored in this branch:

- **DAG inlining** (`DI`, `DagOracle`, `IndexComputer`, and
  `ProgramDisjointness`) from the simplified `mini-corral` architecture.
- **HYDRA semantic partitioning** with sequential search and independent local
  worker prover states; no HTTP, RPC, or multi-machine service is included.

DeepAsserts remains explicitly out of scope. Removed components still include:
- The **concurrency instrumentation** subtree (`StormInstrumentationPass`,
  `Instrumenter`), deep-assert passes, static inlining, and the static-analysis
  stack (`StaticAnalysis`, `WeightDomains`, `Policy`, `LiveVariableAnalysis`,
  `ModSet`, `Coverage`, `ErrorProjection`, `VariableManager`,
  `RewriteCallDontCare`, `WellFormedProg`).
- The `AddOns/` tree (FastAVN, AngelicVerifierNull, AliasAnalysis, PropInst) and
  their regressions.

The stdout signals SMACK greps for are preserved verbatim: `Exhausted recursion
bound of N`, `Verifying program while tracking`, `Program has no bugs`, and
`This assertion can fail`.

## The Boogie 3.5.6 port

The `Boogie.ExecutionEngine` package reference in
[`source/Directory.Build.props`](source/Directory.Build.props) is pinned to
**3.5.6** (`mini-corral` is on 2.9.1). Adapting to that API required, among
other things:

- Keeping `SIBoolControlVC` paired with prover evaluation across program, path,
  and refinement verification, and installing Boogie's `CodeExpr` converter so
  code-expression inputs do not crash stratified bool-control VC generation.
- Preserving the recursion-bound retry behavior after Boogie folded bound
  exhaustion into `Inconclusive`.
- Preserving legacy async-call handling during resolve/typecheck, and
  normalizing procedure links before modifies inference.

## Building and running

Build with [.NET 8](https://dotnet.microsoft.com):

```console
$ dotnet build source/Corral.sln
```

Then run the generated executable:

```console
$ source/Corral/bin/Debug/net8.0/corral input.bpl /recursionBound:10
```

Note that this fork is **not** published to NuGet — `dotnet tool install
--global Corral` installs upstream Corral, not mini-corral.

### SMT solver

Running mini-corral requires [Z3](https://github.com/Z3Prover/z3) on `PATH`. CI
tests against Z3 5.0.0.

### Flags

Only the SMACK-compatible subset is accepted; unknown flags are a usage error.
Run `corral` with no arguments for the same list.

| Flag | Meaning |
| --- | --- |
| `/k:n` | Execution context bound (default 2) |
| `/main:str` | Entry procedure name |
| `/recursionBound:n` | Recursion depth bound (default 1) |
| `/trackAllVars` | Track all shared variables |
| `/useArrayTheory` | Use *extensional* arrays — see the note below |
| `/useProverEvaluate` | Use prover evaluate mode |
| `/timeLimit:n` | Z3 timeout in seconds |
| `/cex:n` | Maximum number of counterexamples (default 1) |
| `/maxStaticLoopBound:n` | Upper bound on minimum loop iterations |
| `/tryCTrace` | Emit a C-style error trace |
| `/noTraceOnDisk` | Do not write trace files to disk |
| `/di` | Enable DAG inlining |
| `/hydra` | Enable sequential HYDRA partition search with DI |
| `/hydraWorkers:n` | Enable local HYDRA with `n` independent workers |
| `/set:HydraStats` | Print DI, partition, replay, scheduling, and SMT statistics |
| `/printDataValues:n` | Print data values in the trace |
| `/v:n` | Verbosity level |
| `/bopt:str` | Pass-through option for Boogie |

`/flags:filename` reads additional flags from `filename`.

### DAG inlining and local HYDRA

`/di` keeps ordinary stratified search but allows mutually exclusive dynamic
calls to share a `StratifiedVC`. `/hydra` adds sequential MUST_REACH/MUST_AVOID
partitioning. `/hydraWorkers:n` reconstructs replayable partitions in independent
SI, DI, and prover states. It publishes a sibling only when an idle worker needs
work; otherwise both children stay on the originating worker's incremental
state. A worker counterexample is confirmed by replaying its fixed partition
decisions and known expansion prefix on the master prover; any remaining inlining
stays inside that leaf and produces the normal Corral trace.

Run the 1/2/4/8-worker benchmark with:

```console
$ scripts/bench-di-hydra.sh
```

By default it uses the ntdriver-derived SMACK BPL corpus under
`$SMACK_TEST_ROOT` (default `/home/shaobo/smack-project/smack/test`) and requires
all ten named inputs so a partial corpus cannot be mistaken for a complete run.
Pass explicit BPL paths to benchmark a smaller or in-repository corpus. Raw logs,
commands, metadata, verdicts, replay/scheduling counts, and reconstruction phase
timings are retained in `$BENCH_RESULTS_DIR`.

**`/useArrayTheory` means something different here than on `mini-corral`.**
Boogie 3.5.6 no longer takes a `/useArrayTheory` switch — array theory is always
on — so the port stopped forwarding one. What is left is the extensionality
setting: the default (flag absent) still adds
`/proverOpt:O:smt.array.extensional=false`, and passing `/useArrayTheory` now
only suppresses that, leaving Z3's extensional arrays in place. The flag is
still accepted and parsed; it just no longer switches array theory on.

## Regressions

The tests live in `test/regression`; each `Files` row gives a `.bpl` path, the
expected outcome (`b` for buggy or `c` for correct), and optional test flags. Run
them all with:

```console
$ cd test/regression && perl check.pl
```

Set `CONFIGURATION=Release` to test the release build, or pass a directory name
to `check.pl` to run just that subset. A single test can also be run directly:

```console
$ cd test/regression/001 && ${CORRAL_EXE} 001.bpl /flags:config
```

Tests for removed features (`/track`, `/concat`, `/cooperative`,
`/staticInlining`, `/stackDepthBound`, `/noTrace`, `fwdbck`) and
the historical distributed HYDRA service remain pruned. DI and local-worker
HYDRA regressions are included; DeepAsserts tests remain absent.

[license-badge]: https://img.shields.io/github/license/shaobo-he/corral?color=blue
[ci]:            https://github.com/shaobo-he/corral/actions/workflows/test.yml?query=branch%3Amini-corral-boogie-3.5.6-refresh
[ci-badge]:      https://github.com/shaobo-he/corral/actions/workflows/test.yml/badge.svg?branch=mini-corral-boogie-3.5.6-refresh

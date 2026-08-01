# mini-corral

[![License][license-badge]](LICENSE.txt)
[![CI][ci-badge]][ci]

**mini-corral** is a trimmed-down [Corral](https://github.com/boogie-org/corral)
tailored for the [SMACK](https://github.com/smackers/smack) verification
toolchain. It keeps only the code paths that SMACK actually exercises (see
SMACK's `top.py` and `svcomp/utils.py`) and drops everything else.

> **Branch note.** This is the `mini-corral-boogie-3.5.6-refresh` branch: the
> `mini-corral` baseline ported from **Boogie 2.9.1 to Boogie 3.5.6**. Its
> verification behavior is meant to match the `mini-corral` branch; only the
> Boogie dependency and the code adapting to its API differ.

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

**Scope is sequential-only.** `/k` still parses, but the concurrency machinery
behind it is gone.

Removed, among others:

- **DAG inlining** (`DI`/`DagOracle`/`IndexComputer`/`ProgramDisjointness`),
  dead since `useDI=false`, plus the forward/backward search and the alternate
  stratified-inlining strategies. `StratifiedInlining.cs` is now the plain
  forward loop, the refinement entry point, and the error reporter.
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
| `/useArrayTheory` | Use Z3's native array theory |
| `/useProverEvaluate` | Use prover evaluate mode |
| `/timeLimit:n` | Z3 timeout in seconds |
| `/cex:n` | Maximum number of counterexamples (default 1) |
| `/maxStaticLoopBound:n` | Upper bound on minimum loop iterations |
| `/tryCTrace` | Emit a C-style error trace |
| `/noTraceOnDisk` | Do not write trace files to disk |
| `/printDataValues:n` | Print data values in the trace |
| `/v:n` | Verbosity level |
| `/bopt:str` | Pass-through option for Boogie |

`/flags:filename` reads additional flags from `filename`.

## Regressions

The tests live in `test/regression` (34 cases listed in `Files`; each line is a
`.bpl` path plus the expected outcome, `b` for buggy or `c` for correct). Run
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
concurrency-dependent tests have been pruned along with the code.

[license-badge]: https://img.shields.io/github/license/shaobo-he/corral?color=blue
[ci]:            https://github.com/shaobo-he/corral/actions/workflows/test.yml?query=branch%3Amini-corral-boogie-3.5.6-refresh
[ci-badge]:      https://github.com/shaobo-he/corral/actions/workflows/test.yml/badge.svg?branch=mini-corral-boogie-3.5.6-refresh

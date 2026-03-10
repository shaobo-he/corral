# Updating Corral's Boogie Dependency from 2.9.1 to 3.5.6

This document describes the changes required to update Corral's Boogie
dependency from version 2.9.1 to 3.5.6. The update was done on the
`mini-corral-update-boogie` branch, targeting the subset of Corral used
by SMACK (the "mini-corral" configuration). The target framework was also
updated from net6.0 to net8.0.

## Table of Contents

1. [NuGet Package Update](#1-nuget-package-update)
2. [API Breaking Changes (Mechanical)](#2-api-breaking-changes-mechanical)
3. [Runtime Fixes (Non-Mechanical)](#3-runtime-fixes-non-mechanical)
4. [SIBoolControlVC and Trace Construction](#4-siboolcontrolvc-and-trace-construction)
5. [Loop Handling: The SIBoolControlVC Passification Bug](#5-loop-handling-the-siboolcontrolvc-passification-bug)
6. [Summary of All Commits](#6-summary-of-all-commits)

---

## 1. NuGet Package Update

**Commit:** `d3867e39`

The Boogie NuGet packages were updated in `source/Directory.Build.props`:

```xml
<!-- Before -->
<PackageReference Include="Boogie.ExecutionEngine" Version="2.9.1" />
<!-- After -->
<PackageReference Include="Boogie.ExecutionEngine" Version="3.5.6" />
```

All Boogie packages (Core, VCGeneration, ExecutionEngine, etc.) are updated
as transitive dependencies.

---

## 2. API Breaking Changes (Mechanical)

These are straightforward find-and-replace changes required by Boogie 3.x
API evolution. All were addressed in commit `d3867e39` and fixup commits
`ce013a98` and `2aa59046`.

### 2.1 CommandLineOptions Singleton Removed

Boogie 2.9.1 used a global singleton `CommandLineOptions.Clo`. In 3.5.6,
options are instance-based.

```csharp
// Before
CommandLineOptions.Install(new CommandLineOptions());
CommandLineOptions.Clo.TypeEncodingMethod = CommandLineOptions.TypeEncoding.Monomorphic;

// After
BoogieUtil.BoogieOptions = new CommandLineOptions(Console.Out, new ConsolePrinter());
BoogieUtil.BoogieOptions.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
```

All references to `CommandLineOptions.Clo.X` become `BoogieUtil.BoogieOptions.X`.
Enum constants moved: `CommandLineOptions.Inlining.Assume` →
`CoreOptions.Inlining.Assume`, `CommandLineOptions.TypeEncoding.Monomorphic` →
`CoreOptions.TypeEncoding.Monomorphic`.

### 2.2 TokenTextWriter Constructor

The 1-arg constructor was removed. All call sites need the options argument:

```csharp
// Before
new TokenTextWriter(Console.Out)
// After
new TokenTextWriter(Console.Out, BoogieUtil.BoogieOptions)
```

### 2.3 QKeyValue.FindBoolAttribute Removed

```csharp
// Before
QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint")
// After
QKeyValue.FindAttribute(impl.Attributes, attr => attr.Key == "entrypoint") != null
```

### 2.4 Procedure Constructor Reordered

The constructor gained new parameters and reordered existing ones:

```csharp
// Before (8 args)
new Procedure(token, name, typeParams, ins, outs, requires, modifies, ensures)

// After (10 args)
new Procedure(token, name, typeParams, ins, outs, false, requires,
              new List<Requires>(), ensures, modifies)
```

Key differences:
- `isPure` (bool) added at position 5 — pass `false`
- `preserves` (`List<Requires>`) added at position 7 — pass
  `new List<Requires>()` (**not** `null`; null causes
  `NullReferenceException` in `Procedure.EmitEnd`)
- `modifies` moved to the end (position 9)

### 2.5 Property Renames (PascalCase)

Boogie 3.x renamed several properties to follow C# conventions:

| Old (2.9.1) | New (3.5.6) |
|---|---|
| `GotoCmd.labelTargets` | `GotoCmd.LabelTargets` |
| `trace.calleeCounterexamples` | `trace.CalleeCounterexamples` |
| `info.counterexample` | `info.Counterexample` |
| `info.args` | `info.Args` |

### 2.6 Program.Typecheck

Now requires an options argument:

```csharp
// Before
program.Typecheck()
// After
program.Typecheck(BoogieUtil.BoogieOptions)
```

### 2.7 Inliner API Changes

The static `Inliner.ProcessImplementation(program, impl, customInliner)`
overload was removed. The new static version doesn't accept a custom inliner:

```csharp
// New static (no custom inliner)
Inliner.ProcessImplementation(CoreOptions, Program, Implementation)
```

For subclasses that need custom inlining behavior, use the instance method
via `base.ProcessImplementation(program, impl)`. The constructor also
requires a 4th argument:

```csharp
// Before
base(program, cb, -1)
// After
base(program, cb, -1, BoogieUtil.BoogieOptions)
```

### 2.8 Removed APIs

- **`YieldCmd`**: Removed entirely in Boogie 3.x. Delete any
  `if (cmd is YieldCmd)` blocks.
- **`.Iter()` extension method**: Removed from `IEnumerable`. Replace with
  `foreach` loops.
- **`impl.SkipVerification`**: Replaced with
  `impl.IsSkipVerification(BoogieUtil.BoogieOptions)`.
- **`Inliner.recursiveProcUnrollMap`**: Removed. Inline count is now
  controlled solely by the `GetInlineCount` return value.

### 2.9 ModSetCollector Null Proc Reference

**Commit:** `2aa59046`

Boogie 3.5.6's `ModSetCollector.VisitCallCmd` uses `callCmd.Proc`
(the `Procedure` object) as a dictionary key. Corral's `FixedDuplicator`
intentionally sets `Proc = null` when `retainProcCalls = false`, causing
`ContainsKey(null)` to throw `ArgumentNullException`.

**Fix:** Re-resolve null `Proc` references in `DoModSetAnalysis` before
calling `CollectModifies`:

```csharp
// In BoogieUtil.DoModSetAnalysis:
// Re-resolve null Proc references before CollectModifies
foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
    foreach (var blk in impl.Blocks)
        foreach (var cmd in blk.Cmds)
            if (cmd is CallCmd cc && cc.Proc == null)
                cc.Proc = program.TopLevelDeclarations.OfType<Procedure>()
                    .FirstOrDefault(p => p.Name == cc.callee);
```

---

## 3. Runtime Fixes (Non-Mechanical)

These are behavioral changes in Boogie 3.5.6 that required logic changes
in Corral, not just API renames.

### 3.1 Removed CLI Switches

**Commit:** `8dc9a8e8`

Two Boogie CLI flags used by Corral were removed in 3.5.6:

- **`/recursionBound`**: Boogie 3.5.6 removed the option parser case.
  Corral already manages recursion bounds via `BoogieUtil.RecursionBound`,
  so the flag is simply dropped from the `boogieOptions` string.

- **`/useArrayTheory`**: Removed because `UseArrayTheory` is now a computed
  property (`!useArrayAxioms && TypeEncodingMethod == Monomorphic`). Since
  Corral sets `TypeEncodingMethod = Monomorphic`, array theory is on by
  default. The flag is removed; only the prover-level extensionality option
  is kept for the weak array theory mode.

### 3.2 prover.Check() Throws NotImplementedException

**Commit:** `71333014`

Boogie 3.5.6's `ProverInterface.Check()` (no-arg overload) is a stub that
throws `NotImplementedException`. The full push/check-sat/pop cycle is now
handled internally by `CheckAssumptions`. Corral's `StratifiedInlining`
had an explicit `prover.Check()` call in the `CheckVC` method that needed
to be removed.

### 3.3 Unsat Core Production Required

**Commit:** `b23fbdce`

Boogie 3.5.6's `CheckAssumptions` unconditionally calls `(get-unsat-core)`
after an unsat result, which requires z3 to have `:produce-unsat-cores`
enabled. Without this, z3 returns an error.

**Fix:** Set `BoogieUtil.BoogieOptions.EnableUnSatCoreExtract = 1` during
Corral initialization so the prover emits
`(set-option :produce-unsat-cores true)`.

---

## 4. SIBoolControlVC and Trace Construction

**Commit:** `e0c16fdd`

### Background

Boogie 2.9.1 used `label2absy` — a mapping from integer labels in the VC
to program statements — for counterexample trace extraction. Boogie 3.5.6
removed `label2absy` entirely. The replacement is **SIBoolControlVC mode**,
which uses boolean control variables to encode the CFG in the VC. Each
block gets a boolean `SIV@N` variable that indicates whether the block was
executed.

### What Changed

When `SIBoolControlVC = true`, Boogie's passification transforms `CallCmd`
instructions into `AssumeCmd` instructions with `NAryExpr` bodies. This
means the trace returned by the prover contains `AssumeCmd` nodes where
`CallCmd` nodes were expected.

### Fixes Required

1. **Enable SIBoolControlVC per-phase**: Added `SIBoolControlVC` field to
   `BoogieVerifyOptions` with per-phase control via `Set()`:

   ```csharp
   // In BoogieVerifyOptions
   public bool SIBoolControlVC;

   // In Set()
   BoogieUtil.BoogieOptions.SIBoolControlVC = SIBoolControlVC;
   ```

   Enabled for both `progVerifyOptions` and `pathVerifyOptions` in
   `ConfigManager.Initialize`.

2. **Handle passified AssumeCmd in trace matching**: In
   `ReconstructImperativeTrace`, the callee name matching loop now handles
   both `CallCmd` and passified `AssumeCmd`:

   ```csharp
   string cmdCalleeName = null;
   if (c is CallCmd cc2)
       cmdCalleeName = cc2.Proc.Name;
   else if (c is AssumeCmd ac && ac.Expr is NAryExpr nary
            && nary.Fun is FunctionCall fc)
       cmdCalleeName = fc.FunctionName;
   ```

3. **Fix FixedDuplicator**: Override `VisitBlockList` (not just the removed
   `VisitBlockSeq`) to prevent shared `Block` references between original
   and copied programs.

4. **Handle non-inlined call sites**: In `StratifiedInlining.NewTrace`,
   record `CalleeCounterexamples` entries for non-inlined call sites too,
   since SIBoolControlVC mode reports them.

5. **Null guards**: Added null checks in `mapBackTrace`,
   `fillInContextSwitchInfo`, and `CBADriver.VerifyProgram` for cases where
   trace construction fails (the trace is null but a bug was still found).

---

## 5. Loop Handling: The SIBoolControlVC Passification Bug

**Commit:** `63b3ae5f`

This was the most complex issue discovered during the update. It required
changes to three files and fixes three distinct sub-problems.

### The Root Cause

SIBoolControlVC passification in Boogie 3.5.6 has a bug where it **drops
variable assignments that precede loop headers** from the generated VC.
For example, if the Boogie program has:

```
$i0 := 1;
goto loop_head;
loop_head:
  // use $i0
```

The assignment `$i0 := 1` is lost in the VC, leaving `$i0` unconstrained.
This was confirmed by examining the SMT log where `$slt.i32($i0, 5)` used
a literal `0` instead of the assigned value.

### The Solution: Explicit Loop Extraction

On master (Boogie 2.9.1), Corral calls `program.ExtractLoops()` which
converts loops into recursive procedures. This call was present in
`BoogieVerify.Verify()`. With Boogie 3.5.6, the API changed to a static
method: `LoopExtractor.ExtractLoops(options, program)`.

Loop extraction eliminates back-edges from the CFG (loops become recursive
procedure calls), which means the SIBoolControlVC passification works
correctly — there are no loop headers for it to mishandle.

```csharp
var extractionInfo = LoopExtractor.ExtractLoops(BoogieUtil.BoogieOptions, program);
program.Resolve(BoogieUtil.BoogieOptions);
program.Typecheck(BoogieUtil.BoogieOptions);
```

### Why Loop Unrolling Doesn't Work

An alternative approach — `LoopUnroll.UnrollLoops()` — was tried but
rejected because:

1. **Nested loops**: Unrolling depth N gives N total iterations across all
   nesting levels. A 5x5 nested loop needs depth 25+, not 6. Loop
   extraction gives each nesting level its own recursion budget.

2. **Trace reconstruction**: Unrolled blocks get `#N` suffixed labels that
   the trace reconstruction code doesn't recognize, causing "intermediate
   block has a procedure call" errors.

### Sub-fix 1: Modifies Clause Propagation

Boogie 3.5.6's `LoopExtractor` does not propagate `modifies` clauses from
callees to extracted loop procedures. Without `modifies` clauses,
StratifiedInlining's over-approximation assumes loop procedures don't
modify any globals. This causes the over-approximation to report "Correct"
prematurely — it never explores the loop deeply enough to find the bug.

**Fix:** After loop extraction, do a fixed-point computation to propagate
`modifies` clauses transitively through all `LoopProcedure` instances:

```csharp
var changed = true;
while (changed)
{
    changed = false;
    foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
    {
        if (!(impl.Proc is LoopProcedure)) continue;
        // Collect globals modified by callees, add to this proc's modifies
        // ... (fixed-point iteration)
    }
}
```

### Sub-fix 2: Recursion Bound Progression

Boogie 2.9.1 had a `VcOutcome.ReachedBound` enum value distinct from
`VcOutcome.Inconclusive`. Corral's `StratifiedInlining` progressively
increases the recursion bound from 1 to `BoogieUtil.RecursionBound`:

```csharp
// Master code
if (outcome == Outcome.Inconclusive) break;        // true inconclusive
if (outcome == Outcome.ReachedBound && curr < max)  // bound hit, retry
    { currRecursionBound++; continue; }
```

Boogie 3.5.6 merged `ReachedBound` into `Inconclusive`. The master logic
would break immediately on `Inconclusive` without ever incrementing the
bound, preventing exploration beyond depth 1.

**Fix:** Distinguish "reached bound" from "true inconclusive" by checking
`procsHitRecBound`:

```csharp
if (outcome == Outcome.OutOfMemory || outcome == Outcome.TimedOut)
    break;
if (outcome == VcOutcome.Inconclusive
    && procsHitRecBound.Count > 0
    && currRecursionBound < BoogieUtil.RecursionBound)
{
    currRecursionBound++;
    continue;
}
if (outcome == Outcome.Inconclusive) break;
```

### Sub-fix 3: Trace Mapping Across Loop Extraction

After loop extraction, counterexample traces reference extracted loop
procedure blocks (e.g., `main_loop_$bb1`) that don't exist in the original
program. Boogie provides `ExtractLoopTrace` to map these back:

```csharp
if (extractionInfo != null)
{
    errors[i] = vcgen.ExtractLoopTrace(
        errors[i], impl.Name, program, extractionInfo);
}
```

This call is inserted before `ReconstructImperativeTrace` in the error
processing loop. The `extractionInfo` dictionary is the return value from
`LoopExtractor.ExtractLoops()`.

---

## 6. Summary of All Commits

| Commit | Description |
|--------|-------------|
| `d3867e39` | Initial Boogie 2.9.1 → 3.5.6 update (all mechanical API changes) |
| `ce013a98` | Fix `NullReferenceException` in `Procedure.EmitEnd` (null preserves list) |
| `2aa59046` | Fix `ArgumentNullException` in `ModSetCollector` (null Proc reference) |
| `8dc9a8e8` | Remove `/recursionBound` and `/useArrayTheory` CLI flags |
| `71333014` | Remove `prover.Check()` call (throws `NotImplementedException`) |
| `b23fbdce` | Enable unsat core production for `CheckAssumptions` compatibility |
| `e0c16fdd` | Fix trace construction for SIBoolControlVC mode |
| `63b3ae5f` | Fix SIBoolControlVC passification bug with loops |

### Files Modified

The update touched 28 files in the initial commit. Post-fix commits
modified primarily:

- `source/CoreLib/BoogieVerify.cs` — Central verification logic, loop
  extraction, trace reconstruction
- `source/CoreLib/StratifiedInlining.cs` — Recursion bound progression,
  trace building, prover interaction
- `source/Corral/Driver.cs` — CLI option handling, Boogie initialization
- `source/Corral/CBADriver.cs` — Per-phase SIBoolControlVC configuration
- `source/Util/BoogieUtil.cs` — ModSetCollector fix, utility functions
- `source/Util/Duplicator.cs` — FixedDuplicator block list handling

### Testing

The update was validated against SMACK-generated Boogie programs:

1. **No-bug programs** correctly report "Program has no bugs"
2. **Simple assertion failures** (single loop, `--unroll=11`) correctly
   report the bug with full execution trace
3. **Nested loop assertion failures** (`--unroll=6`, 5x5 nested loops)
   correctly report the bug with 25 loop iterations in the trace

The output format matches master's behavior: SMACK patterns like
"can fail", "no bugs", and "Execution trace:" are preserved.

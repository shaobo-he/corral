using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading;

namespace CoreLib
{
    public enum SiCheckKind
    {
        Under,
        Over,
        Other
    }

    /// <summary>
    /// Opt-in, process-local recorder for stratified-inlining diagnostics.
    /// Set CORRAL_SI_PROFILE to a TSV path to enable it.  In the normal case the
    /// only cost is an IsEnabled branch at each instrumentation point.
    /// </summary>
    public static class SiProfile
    {
        private static readonly string[] Columns =
        {
            "record_type", "timestamp_ms", "benchmark", "cegar_iter", "phase", "implementation", "si_mode",
            "bound", "si_iter", "check_kind", "query_id", "callee", "callsite_id",
            "reason", "result", "duration_ms", "query_ms", "under_result",
            "over_result", "under_ms", "over_ms", "under_checks", "over_checks",
            "other_checks", "under_smt_ms", "over_smt_ms", "other_smt_ms",
            "max_under_ms", "max_over_ms", "open_calls", "max_open_calls",
            "bound_blocked", "unique_bound_procs", "requested_expansions",
            "actual_expansions", "new_open_calls", "total_inlined", "fresh_vcs",
            "di_merges", "vc_size", "vc_added", "stack_depth", "rec_depth",
            "max_stack_depth", "max_rec_depth", "tracked_vars", "total_vars",
            "count", "program_verify_ms", "concretize_ms", "refinement_ms",
            "program_smt_ms", "concretize_smt_ms", "refinement_smt_ms",
            "stack_hist", "rec_hist", "top_callees", "prover_log", "details",
            "helper_requested", "helper_deferred", "helper_expanded",
            "helper_not_expanded", "helper_vc_avoided", "extra_over_queries",
            "helper_survival_rate", "outline_mode", "outlined_regions",
            "synthetic_procs", "original_blocks", "caller_blocks_after",
            "region_blocks", "region_cmds", "region_calls", "live_ins",
            "live_outs", "internal_locals"
        };

        private static readonly Dictionary<string, int> ColumnIndexes = Columns
            .Select((name, index) => (name, index))
            .ToDictionary(pair => pair.name, pair => pair.index);
        private static readonly object Gate = new object();
        private static readonly Stopwatch RunClock = new Stopwatch();
        private static StreamWriter writer;
        private static bool initialized;
        private static string benchmark = "";
        private static string phase = "OTHER";
        private static string currentImplementation = "";
        private static string currentSiMode = "";
        private static int cegarIteration;
        private static int trackedVariables;
        private static int totalVariables;
        private static long nextQueryId;
        private static long totalUnderChecks;
        private static long totalOverChecks;
        private static long totalOtherChecks;
        private static long totalUnderMilliseconds;
        private static long totalOverMilliseconds;
        private static long totalOtherMilliseconds;
        private static long programSmtMilliseconds;
        private static long concretizeSmtMilliseconds;
        private static long refinementSmtMilliseconds;
        private static long totalExpansions;
        private static long totalFreshVcs;
        private static long totalDiMerges;
        private static long totalBounds;
        private static int maximumBound;
        private static int maximumStackDepth;
        private static int maximumRecursionDepth;

        public static bool IsEnabled => writer != null;
        public static bool LogIterations { get; private set; } = true;
        public static bool LogExpansions { get; private set; }
        public static bool LogQueryStarts { get; private set; }
        public static long SlowQueryMilliseconds { get; private set; } = 500;
        public static long DumpSlowQueryMilliseconds { get; private set; } = -1;
        public static string Phase => phase;
        public static int CegarIteration => cegarIteration;

        public static void StartRun(string inputFile)
        {
            lock (Gate)
            {
                if (initialized)
                    return;

                initialized = true;
                var path = Environment.GetEnvironmentVariable("CORRAL_SI_PROFILE");
                if (string.IsNullOrWhiteSpace(path))
                    return;

                var directory = Path.GetDirectoryName(Path.GetFullPath(path));
                if (!string.IsNullOrEmpty(directory))
                    Directory.CreateDirectory(directory);

                writer = new StreamWriter(new FileStream(path, FileMode.Create, FileAccess.Write, FileShare.Read));
                writer.AutoFlush = false;
                benchmark = inputFile ?? "";
                SlowQueryMilliseconds = ReadLongEnvironment("CORRAL_SI_SLOW_MS", 500);
                DumpSlowQueryMilliseconds = ReadLongEnvironment("CORRAL_SI_DUMP_SLOW_MS", -1);
                LogIterations = ReadBoolEnvironment("CORRAL_SI_PROFILE_ITERATIONS", true);
                LogExpansions = ReadBoolEnvironment("CORRAL_SI_PROFILE_EXPANSIONS", false);
                LogQueryStarts = ReadBoolEnvironment("CORRAL_SI_PROFILE_QUERY_START", false);
                RunClock.Restart();
                writer.WriteLine(string.Join("\t", Columns));
                Write("META",
                    ("details", "vc_size=structural_node_estimate;di_available=false;stingy_available=false"),
                    ("reason", "profile_start"));
            }
        }

        public static void EndRun(string result = "completed")
        {
            lock (Gate)
            {
                if (writer == null)
                    return;

                WriteUnlocked("SUMMARY",
                    ("result", result),
                    ("duration_ms", Milliseconds(RunClock.Elapsed).ToString(CultureInfo.InvariantCulture)),
                    ("under_checks", totalUnderChecks.ToString(CultureInfo.InvariantCulture)),
                    ("over_checks", totalOverChecks.ToString(CultureInfo.InvariantCulture)),
                    ("other_checks", totalOtherChecks.ToString(CultureInfo.InvariantCulture)),
                    ("under_smt_ms", totalUnderMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("over_smt_ms", totalOverMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("other_smt_ms", totalOtherMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("program_smt_ms", programSmtMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("concretize_smt_ms", concretizeSmtMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("refinement_smt_ms", refinementSmtMilliseconds.ToString(CultureInfo.InvariantCulture)),
                    ("actual_expansions", totalExpansions.ToString(CultureInfo.InvariantCulture)),
                    ("fresh_vcs", totalFreshVcs.ToString(CultureInfo.InvariantCulture)),
                    ("di_merges", totalDiMerges.ToString(CultureInfo.InvariantCulture)),
                    ("bound", maximumBound.ToString(CultureInfo.InvariantCulture)),
                    ("count", totalBounds.ToString(CultureInfo.InvariantCulture)),
                    ("max_stack_depth", maximumStackDepth.ToString(CultureInfo.InvariantCulture)),
                    ("max_rec_depth", maximumRecursionDepth.ToString(CultureInfo.InvariantCulture)));
                writer.Dispose();
                writer = null;
                RunClock.Stop();
            }
        }

        public static long NextQueryId()
        {
            return Interlocked.Increment(ref nextQueryId);
        }

        public static void SetCegarContext(int iteration, int tracked, int total)
        {
            if (!IsEnabled)
                return;
            cegarIteration = iteration;
            trackedVariables = tracked;
            totalVariables = total;
        }

        public static int NextCegarIteration(int tracked, int total)
        {
            if (!IsEnabled)
                return 0;
            SetCegarContext(cegarIteration + 1, tracked, total);
            return cegarIteration;
        }

        public static void SetSiContext(string implementation, string mode)
        {
            if (!IsEnabled)
                return;
            currentImplementation = implementation ?? "";
            currentSiMode = mode ?? "";
        }

        public static IDisposable EnterPhase(string newPhase)
        {
            if (!IsEnabled)
                return NoopScope.Instance;
            var oldPhase = phase;
            phase = newPhase ?? "OTHER";
            return new Scope(() => phase = oldPhase);
        }

        public static void RecordQuery(SiCheckKind kind, long milliseconds)
        {
            if (!IsEnabled)
                return;
            switch (kind)
            {
                case SiCheckKind.Under:
                    totalUnderChecks++;
                    totalUnderMilliseconds += milliseconds;
                    break;
                case SiCheckKind.Over:
                    totalOverChecks++;
                    totalOverMilliseconds += milliseconds;
                    break;
                default:
                    totalOtherChecks++;
                    totalOtherMilliseconds += milliseconds;
                    break;
            }
            if (phase == "PROGRAM")
                programSmtMilliseconds += milliseconds;
            else if (phase == "CONCRETIZE")
                concretizeSmtMilliseconds += milliseconds;
            else if (phase == "REFINEMENT")
                refinementSmtMilliseconds += milliseconds;
        }

        public static void RecordBound(int bound)
        {
            if (!IsEnabled)
                return;
            totalBounds++;
            maximumBound = Math.Max(maximumBound, bound);
        }

        public static void RecordDepths(int stackDepth, int recursionDepth)
        {
            if (!IsEnabled)
                return;
            maximumStackDepth = Math.Max(maximumStackDepth, stackDepth);
            maximumRecursionDepth = Math.Max(maximumRecursionDepth, recursionDepth);
        }

        public static void RecordExpansion(int freshVcs, int diMerges)
        {
            if (!IsEnabled)
                return;
            totalExpansions++;
            totalFreshVcs += freshVcs;
            totalDiMerges += diMerges;
        }

        public static void Write(string recordType, params (string key, string value)[] values)
        {
            lock (Gate)
            {
                if (writer == null)
                    return;
                WriteUnlocked(recordType, values);
            }
        }

        public static string Ms(TimeSpan elapsed)
        {
            return Milliseconds(elapsed).ToString(CultureInfo.InvariantCulture);
        }

        public static string Number(long value)
        {
            return value.ToString(CultureInfo.InvariantCulture);
        }

        public static string Number(double value)
        {
            return value.ToString("F3", CultureInfo.InvariantCulture);
        }

        private static void WriteUnlocked(string recordType, params (string key, string value)[] values)
        {
            var fields = new string[Columns.Length];
            fields[ColumnIndexes["record_type"]] = recordType;
            fields[ColumnIndexes["timestamp_ms"]] = Milliseconds(RunClock.Elapsed).ToString(CultureInfo.InvariantCulture);
            fields[ColumnIndexes["benchmark"]] = benchmark;
            fields[ColumnIndexes["cegar_iter"]] = cegarIteration == 0 ? "" : cegarIteration.ToString(CultureInfo.InvariantCulture);
            fields[ColumnIndexes["phase"]] = phase;
            fields[ColumnIndexes["implementation"]] = currentImplementation;
            fields[ColumnIndexes["si_mode"]] = currentSiMode;
            fields[ColumnIndexes["tracked_vars"]] = trackedVariables == 0 ? "" : trackedVariables.ToString(CultureInfo.InvariantCulture);
            fields[ColumnIndexes["total_vars"]] = totalVariables == 0 ? "" : totalVariables.ToString(CultureInfo.InvariantCulture);
            foreach (var (key, value) in values)
            {
                if (ColumnIndexes.TryGetValue(key, out var index))
                    fields[index] = value;
            }
            writer.WriteLine(string.Join("\t", fields.Select(Escape)));
            if (recordType != "SI_ITER" && recordType != "EXPAND")
                writer.Flush();
        }

        private static string Escape(string value)
        {
            return (value ?? "").Replace("\\", "\\\\").Replace("\t", "\\t").Replace("\r", "\\r").Replace("\n", "\\n");
        }

        private static long Milliseconds(TimeSpan elapsed)
        {
            return (long)Math.Round(elapsed.TotalMilliseconds);
        }

        private static long ReadLongEnvironment(string name, long fallback)
        {
            var text = Environment.GetEnvironmentVariable(name);
            return long.TryParse(text, NumberStyles.Integer, CultureInfo.InvariantCulture, out var value) ? value : fallback;
        }

        private static bool ReadBoolEnvironment(string name, bool fallback)
        {
            var text = Environment.GetEnvironmentVariable(name);
            if (string.IsNullOrWhiteSpace(text))
                return fallback;
            return text != "0" && !text.Equals("false", StringComparison.OrdinalIgnoreCase);
        }

        private sealed class Scope : IDisposable
        {
            private Action onDispose;
            public Scope(Action onDispose) { this.onDispose = onDispose; }
            public void Dispose()
            {
                var action = Interlocked.Exchange(ref onDispose, null);
                action?.Invoke();
            }
        }

        private sealed class NoopScope : IDisposable
        {
            public static readonly NoopScope Instance = new NoopScope();
            public void Dispose() { }
        }
    }

    internal sealed class SiVerificationProfile
    {
        internal readonly struct CallsitePoint
        {
            public readonly string Callee;
            public readonly string Id;
            public readonly int StackDepth;
            public readonly int RecursionDepth;
            public readonly bool Fresh;

            public CallsitePoint(string callee, string id, int stackDepth, int recursionDepth, bool fresh)
            {
                Callee = callee;
                Id = id;
                StackDepth = stackDepth;
                RecursionDepth = recursionDepth;
                Fresh = fresh;
            }
        }

        private sealed class ExpansionAggregate
        {
            public long Expansions;
            public long FreshVcs;
            public long Merges;
            public long VcAdded;
            public long StackDepthSum;
            public int MaxVcAdded;
            public int MaxStackDepth;
            public int MaxRecursionDepth;
        }

        private sealed class BoundHitAggregate
        {
            public string Callee;
            public string Id;
            public string Reason;
            public long Count;
            public int StackDepth;
            public int RecursionDepth;
        }

        private readonly struct Snapshot
        {
            public readonly long UnderChecks;
            public readonly long OverChecks;
            public readonly long OtherChecks;
            public readonly long UnderMilliseconds;
            public readonly long OverMilliseconds;
            public readonly long OtherMilliseconds;
            public readonly long Expansions;
            public readonly long FreshVcs;
            public readonly long DiMerges;

            public Snapshot(SiVerificationProfile profile)
            {
                UnderChecks = profile.underChecks;
                OverChecks = profile.overChecks;
                OtherChecks = profile.otherChecks;
                UnderMilliseconds = profile.underMilliseconds;
                OverMilliseconds = profile.overMilliseconds;
                OtherMilliseconds = profile.otherMilliseconds;
                Expansions = profile.expansions;
                FreshVcs = profile.freshVcs;
                DiMerges = profile.diMerges;
            }
        }

        private readonly string implementation;
        private readonly string mode;
        private readonly string proverLog;
        private readonly Stopwatch verificationClock = Stopwatch.StartNew();
        private readonly Stopwatch boundClock = new Stopwatch();
        private readonly Stopwatch fwdClock = new Stopwatch();
        private readonly Dictionary<string, ExpansionAggregate> expansionsByCallee = new Dictionary<string, ExpansionAggregate>();
        private readonly Dictionary<int, long> expansionStackHistogram = new Dictionary<int, long>();
        private readonly Dictionary<int, long> expansionRecursionHistogram = new Dictionary<int, long>();
        private readonly Dictionary<string, BoundHitAggregate> boundHits = new Dictionary<string, BoundHitAggregate>();
        private Snapshot fwdStart;
        private long underChecks;
        private long overChecks;
        private long otherChecks;
        private long underMilliseconds;
        private long overMilliseconds;
        private long otherMilliseconds;
        private long maxUnderMilliseconds;
        private long maxOverMilliseconds;
        private long expansions;
        private long fwdMaxUnderMilliseconds;
        private long fwdMaxOverMilliseconds;
        private long totalBlockedAtBound;
        private long freshVcs;
        private long diMerges;
        private long vcSize;
        private long blockedAtBound;
        private int maxOpenCalls;
        private int fwdMaxOpenCalls;
        private int maxStackDepth;
        private int maxRecursionDepth;
        private long helperRequested;
        private long helperDeferred;
        private long helperExpanded;
        private long helperExpandedVc;
        private long extraOverQueries;
        private readonly HashSet<string> deferredHelperIds = new HashSet<string>();
        private readonly HashSet<string> expandedHelperIds = new HashSet<string>();

        public int Bound { get; private set; }
        public int Iteration { get; private set; }
        public int MaxStackDepth => maxStackDepth;
        public int MaxRecursionDepth => maxRecursionDepth;
        public long VcSize => vcSize;
        public long TotalInlined => expansions;
        public long FreshVcs => freshVcs;
        public long DiMerges => diMerges;

        public SiVerificationProfile(string implementation, string mode, int rootVcSize, int initialOpenCalls, string proverLog)
        {
            this.implementation = implementation ?? "";
            this.mode = mode ?? "SI";
            this.proverLog = proverLog ?? "";
            SiProfile.SetSiContext(this.implementation, this.mode);
            vcSize = rootVcSize;
            maxOpenCalls = initialOpenCalls;
            if (initialOpenCalls > 0)
            {
                maxStackDepth = 1;
                maxRecursionDepth = 1;
            }
            SiProfile.Write("SI_START",
                Common(),
                ("open_calls", SiProfile.Number(initialOpenCalls)),
                ("vc_size", SiProfile.Number(vcSize)));
        }

        public void ObserveCallsite(int stackDepth, int recursionDepth)
        {
            maxStackDepth = Math.Max(maxStackDepth, stackDepth);
            maxRecursionDepth = Math.Max(maxRecursionDepth, recursionDepth);
        }

        public void StartBound(int bound, int openCalls)
        {
            Bound = bound;
            Iteration = 0;
            blockedAtBound = 0;
            boundHits.Clear();
            maxOpenCalls = Math.Max(maxOpenCalls, openCalls);
            boundClock.Restart();
            SiProfile.Write("BOUND_START",
                Common(),
                ("bound", SiProfile.Number(bound)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("total_inlined", SiProfile.Number(expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs)),
                ("di_merges", SiProfile.Number(diMerges)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public void EndBound(string outcome, bool reachedBound, int openCalls)
        {
            boundClock.Stop();
            SiProfile.RecordBound(Bound);
            foreach (var hit in boundHits.Values.OrderByDescending(item => item.Count).ThenBy(item => item.Callee))
            {
                SiProfile.Write("BOUND_HIT",
                    Common(),
                    ("bound", SiProfile.Number(Bound)),
                    ("callee", hit.Callee),
                    ("callsite_id", hit.Id),
                    ("reason", hit.Reason),
                    ("count", SiProfile.Number(hit.Count)),
                    ("stack_depth", SiProfile.Number(hit.StackDepth)),
                    ("rec_depth", SiProfile.Number(hit.RecursionDepth)));
            }
            SiProfile.Write("BOUND_END",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("result", reachedBound ? "ReachedBound" : outcome),
                ("duration_ms", SiProfile.Ms(boundClock.Elapsed)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("bound_blocked", SiProfile.Number(blockedAtBound)),
                ("unique_bound_procs", SiProfile.Number(boundHits.Values.Select(hit => hit.Callee).Distinct().Count())),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public void StartFwd(int openCalls)
        {
            fwdStart = new Snapshot(this);
            fwdMaxUnderMilliseconds = 0;
            fwdMaxOverMilliseconds = 0;
            fwdMaxOpenCalls = openCalls;
            maxOpenCalls = Math.Max(maxOpenCalls, openCalls);
            fwdClock.Restart();
            SiProfile.Write("FWD_START",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("total_inlined", SiProfile.Number(expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs)),
                ("di_merges", SiProfile.Number(diMerges)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public void EndFwd(string outcome, int openCalls)
        {
            fwdClock.Stop();
            fwdMaxOpenCalls = Math.Max(fwdMaxOpenCalls, openCalls);
            maxOpenCalls = Math.Max(maxOpenCalls, openCalls);
            SiProfile.Write("FWD_END",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("result", outcome),
                ("duration_ms", SiProfile.Ms(fwdClock.Elapsed)),
                ("under_checks", SiProfile.Number(underChecks - fwdStart.UnderChecks)),
                ("over_checks", SiProfile.Number(overChecks - fwdStart.OverChecks)),
                ("other_checks", SiProfile.Number(otherChecks - fwdStart.OtherChecks)),
                ("under_smt_ms", SiProfile.Number(underMilliseconds - fwdStart.UnderMilliseconds)),
                ("over_smt_ms", SiProfile.Number(overMilliseconds - fwdStart.OverMilliseconds)),
                ("other_smt_ms", SiProfile.Number(otherMilliseconds - fwdStart.OtherMilliseconds)),
                ("actual_expansions", SiProfile.Number(expansions - fwdStart.Expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs - fwdStart.FreshVcs)),
                ("di_merges", SiProfile.Number(diMerges - fwdStart.DiMerges)),
                ("max_under_ms", SiProfile.Number(fwdMaxUnderMilliseconds)),
                ("max_over_ms", SiProfile.Number(fwdMaxOverMilliseconds)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("max_open_calls", SiProfile.Number(fwdMaxOpenCalls)),
                ("bound_blocked", SiProfile.Number(blockedAtBound)),
                ("total_inlined", SiProfile.Number(expansions)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public int StartIteration(int openCalls)
        {
            Iteration++;
            fwdMaxOpenCalls = Math.Max(fwdMaxOpenCalls, openCalls);
            maxOpenCalls = Math.Max(maxOpenCalls, openCalls);
            return Iteration;
        }

        public void RecordIteration(string underResult, long underMs, string overResult, long overMs,
            int openCalls, int requested, long expansionStart, int newOpenCalls)
        {
            fwdMaxOpenCalls = Math.Max(fwdMaxOpenCalls, openCalls);
            maxOpenCalls = Math.Max(maxOpenCalls, openCalls);
            if (!SiProfile.LogIterations)
                return;
            SiProfile.Write("SI_ITER",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("si_iter", SiProfile.Number(Iteration)),
                ("under_result", underResult ?? ""),
                ("over_result", overResult ?? ""),
                ("under_ms", SiProfile.Number(underMs)),
                ("over_ms", SiProfile.Number(overMs)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("requested_expansions", SiProfile.Number(requested)),
                ("actual_expansions", SiProfile.Number(expansions - expansionStart)),
                ("new_open_calls", SiProfile.Number(newOpenCalls)),
                ("total_inlined", SiProfile.Number(expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs)),
                ("di_merges", SiProfile.Number(diMerges)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public void RecordQuery(long queryId, SiCheckKind kind, string outcome, long milliseconds,
            int openCalls, int blockedCalls)
        {
            switch (kind)
            {
                case SiCheckKind.Under:
                    underChecks++;
                    underMilliseconds += milliseconds;
                    maxUnderMilliseconds = Math.Max(maxUnderMilliseconds, milliseconds);
                    fwdMaxUnderMilliseconds = Math.Max(fwdMaxUnderMilliseconds, milliseconds);
                    break;
                case SiCheckKind.Over:
                    overChecks++;
                    overMilliseconds += milliseconds;
                    maxOverMilliseconds = Math.Max(maxOverMilliseconds, milliseconds);
                    fwdMaxOverMilliseconds = Math.Max(fwdMaxOverMilliseconds, milliseconds);
                    break;
                default:
                    otherChecks++;
                    otherMilliseconds += milliseconds;
                    break;
            }
            SiProfile.RecordQuery(kind, milliseconds);
            if (SiProfile.LogQueryStarts)
            {
                SiProfile.Write("SMT_END",
                    Common(),
                    ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                    ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                    ("check_kind", kind.ToString().ToUpperInvariant()),
                    ("query_id", SiProfile.Number(queryId)),
                    ("result", outcome),
                    ("query_ms", SiProfile.Number(milliseconds)));
            }
            if (milliseconds >= SiProfile.SlowQueryMilliseconds)
            {
                SiProfile.Write("SMT",
                    Common(),
                    ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                    ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                    ("check_kind", kind.ToString().ToUpperInvariant()),
                    ("query_id", SiProfile.Number(queryId)),
                    ("result", outcome),
                    ("query_ms", SiProfile.Number(milliseconds)),
                    ("open_calls", SiProfile.Number(openCalls)),
                    ("bound_blocked", SiProfile.Number(blockedCalls)),
                    ("total_inlined", SiProfile.Number(expansions)),
                    ("fresh_vcs", SiProfile.Number(freshVcs)),
                    ("di_merges", SiProfile.Number(diMerges)),
                    ("vc_size", SiProfile.Number(vcSize)),
                    ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                    ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
            }
            if (SiProfile.DumpSlowQueryMilliseconds >= 0 && milliseconds >= SiProfile.DumpSlowQueryMilliseconds)
            {
                SiProfile.Write("SLOW_QUERY",
                    Common(),
                    ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                    ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                    ("check_kind", kind.ToString().ToUpperInvariant()),
                    ("query_id", SiProfile.Number(queryId)),
                    ("query_ms", SiProfile.Number(milliseconds)),
                    ("result", outcome),
                    ("prover_log", proverLog),
                    ("details", string.IsNullOrEmpty(proverLog)
                        ? "rerun with Boogie prover logging enabled; query is bracketed by CORRAL_SI_QUERY comments"
                        : "locate query between CORRAL_SI_QUERY_BEGIN/END comments"));
            }
        }

        public void RecordQueryStart(long queryId, SiCheckKind kind, int openCalls, int blockedCalls)
        {
            if (!SiProfile.LogQueryStarts)
                return;
            SiProfile.Write("SMT_START",
                Common(),
                ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                ("check_kind", kind.ToString().ToUpperInvariant()),
                ("query_id", SiProfile.Number(queryId)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("bound_blocked", SiProfile.Number(blockedCalls)),
                ("total_inlined", SiProfile.Number(expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs)),
                ("di_merges", SiProfile.Number(diMerges)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
        }

        public void RecordBoundHit(string callee, string id, int stackDepth, int recursionDepth, string reason)
        {
            blockedAtBound++;
            totalBlockedAtBound++;
            var key = id ?? callee ?? "";
            if (!boundHits.TryGetValue(key, out var aggregate))
            {
                aggregate = new BoundHitAggregate
                {
                    Callee = callee ?? "",
                    Id = id ?? "",
                    Reason = reason ?? "",
                    StackDepth = stackDepth,
                    RecursionDepth = recursionDepth
                };
                boundHits.Add(key, aggregate);
            }
            aggregate.Count++;
        }

        public void RecordOverRequest(IEnumerable<CallsitePoint> callsites)
        {
            var points = callsites.ToList();
            var stackHistogram = Histogram(points.GroupBy(point => point.StackDepth));
            var recursionHistogram = Histogram(points.GroupBy(point => point.RecursionDepth));
            var topCallees = string.Join(",", points.GroupBy(point => point.Callee)
                .OrderByDescending(group => group.Count()).ThenBy(group => group.Key)
                .Take(10).Select(group => group.Key + ":" + group.Count()));
            SiProfile.Write("OVER_EXPAND_REQUEST",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("si_iter", SiProfile.Number(Iteration)),
                ("requested_expansions", SiProfile.Number(points.Count)),
                ("fresh_vcs", SiProfile.Number(points.Count(point => point.Fresh))),
                ("di_merges", SiProfile.Number(points.Count(point => !point.Fresh))),
                ("stack_hist", stackHistogram),
                ("rec_hist", recursionHistogram),
                ("top_callees", topCallees));
        }

        public void RecordBitwiseDeferral(IEnumerable<CallsitePoint> helpers, int normalSelected)
        {
            var points = helpers.ToList();
            helperDeferred += points.Count;
            extraOverQueries++;
            foreach (var point in points)
                deferredHelperIds.Add(point.Id);
            var survived = deferredHelperIds.Intersect(expandedHelperIds).Count();
            var pending = deferredHelperIds.Count - survived;
            SiProfile.Write("BITWISE_DEFER",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("si_iter", SiProfile.Number(Iteration)),
                ("count", SiProfile.Number(points.Count)),
                ("helper_requested", SiProfile.Number(helperRequested)),
                ("helper_deferred", SiProfile.Number(helperDeferred)),
                ("helper_expanded", SiProfile.Number(helperExpanded)),
                ("helper_not_expanded", SiProfile.Number(pending)),
                ("helper_survival_rate", SiProfile.Number(deferredHelperIds.Count == 0 ? 0.0 :
                    (double)survived / deferredHelperIds.Count)),
                ("requested_expansions", SiProfile.Number(normalSelected + points.Count)),
                ("actual_expansions", SiProfile.Number(normalSelected)),
                ("extra_over_queries", SiProfile.Number(extraOverQueries)),
                ("top_callees", string.Join(",", points.GroupBy(point => point.Callee)
                    .OrderByDescending(group => group.Count()).ThenBy(group => group.Key)
                    .Select(group => group.Key + ":" + group.Count()))));
        }

        public void RecordBitwiseRequest(int helperCount)
        {
            helperRequested += helperCount;
            if (helperCount == 0)
                return;
            SiProfile.Write("BITWISE_REQUEST",
                Common(),
                ("bound", SiProfile.Number(Bound)),
                ("si_iter", SiProfile.Number(Iteration)),
                ("count", SiProfile.Number(helperCount)),
                ("helper_requested", SiProfile.Number(helperRequested)),
                ("helper_deferred", SiProfile.Number(helperDeferred)),
                ("helper_expanded", SiProfile.Number(helperExpanded)),
                ("extra_over_queries", SiProfile.Number(extraOverQueries)));
        }

        public void RecordBitwiseExpansion(string id, int vcAdded)
        {
            helperExpanded++;
            helperExpandedVc += vcAdded;
            expandedHelperIds.Add(id ?? "");
            var survived = deferredHelperIds.Intersect(expandedHelperIds).Count();
            var pending = deferredHelperIds.Count - survived;
            SiProfile.Write("BITWISE_EXPAND",
                Common(),
                ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                ("callsite_id", id ?? ""),
                ("count", "1"),
                ("helper_requested", SiProfile.Number(helperRequested)),
                ("helper_deferred", SiProfile.Number(helperDeferred)),
                ("helper_expanded", SiProfile.Number(helperExpanded)),
                ("helper_not_expanded", SiProfile.Number(pending)),
                ("helper_survival_rate", SiProfile.Number(deferredHelperIds.Count == 0 ? 0.0 :
                    (double)survived / deferredHelperIds.Count)),
                ("extra_over_queries", SiProfile.Number(extraOverQueries)),
                ("vc_added", SiProfile.Number(vcAdded)));
        }

        public void RecordExpansion(string callee, string reason, int stackDepth, int recursionDepth,
            int vcAdded, int newOpenCalls, bool fresh)
        {
            expansions++;
            if (fresh)
                freshVcs++;
            else
                diMerges++;
            vcSize += vcAdded;
            ObserveCallsite(stackDepth, recursionDepth);
            Increment(expansionStackHistogram, stackDepth);
            Increment(expansionRecursionHistogram, recursionDepth);
            if (!expansionsByCallee.TryGetValue(callee, out var aggregate))
            {
                aggregate = new ExpansionAggregate();
                expansionsByCallee.Add(callee, aggregate);
            }
            aggregate.Expansions++;
            aggregate.FreshVcs += fresh ? 1 : 0;
            aggregate.Merges += fresh ? 0 : 1;
            aggregate.VcAdded += vcAdded;
            aggregate.MaxVcAdded = Math.Max(aggregate.MaxVcAdded, vcAdded);
            aggregate.StackDepthSum += stackDepth;
            aggregate.MaxStackDepth = Math.Max(aggregate.MaxStackDepth, stackDepth);
            aggregate.MaxRecursionDepth = Math.Max(aggregate.MaxRecursionDepth, recursionDepth);
            SiProfile.RecordExpansion(fresh ? 1 : 0, fresh ? 0 : 1);
            if (SiProfile.LogExpansions)
            {
                SiProfile.Write("EXPAND",
                    Common(),
                    ("bound", Bound == 0 ? "" : SiProfile.Number(Bound)),
                    ("si_iter", Iteration == 0 ? "" : SiProfile.Number(Iteration)),
                    ("callee", callee),
                    ("reason", reason),
                    ("fresh_vcs", fresh ? "1" : "0"),
                    ("di_merges", fresh ? "0" : "1"),
                    ("vc_added", SiProfile.Number(vcAdded)),
                    ("new_open_calls", SiProfile.Number(newOpenCalls)),
                    ("total_inlined", SiProfile.Number(expansions)),
                    ("vc_size", SiProfile.Number(vcSize)),
                    ("stack_depth", SiProfile.Number(stackDepth)),
                    ("rec_depth", SiProfile.Number(recursionDepth)));
            }
        }

        public void Finish(string outcome, int openCalls)
        {
            SiProfile.RecordDepths(maxStackDepth, maxRecursionDepth);
            verificationClock.Stop();
            foreach (var pair in expansionsByCallee.OrderByDescending(pair => pair.Value.VcAdded)
                         .ThenByDescending(pair => pair.Value.Expansions).ThenBy(pair => pair.Key))
            {
                var aggregate = pair.Value;
                SiProfile.Write("EXPANSION_CALLEE",
                    Common(),
                    ("callee", pair.Key),
                    ("count", SiProfile.Number(aggregate.Expansions)),
                    ("actual_expansions", SiProfile.Number(aggregate.Expansions)),
                    ("fresh_vcs", SiProfile.Number(aggregate.FreshVcs)),
                    ("di_merges", SiProfile.Number(aggregate.Merges)),
                    ("vc_added", SiProfile.Number(aggregate.VcAdded)),
                    ("max_stack_depth", SiProfile.Number(aggregate.MaxStackDepth)),
                    ("max_rec_depth", SiProfile.Number(aggregate.MaxRecursionDepth)),
                    ("details", "max_vc_added=" + aggregate.MaxVcAdded + ";avg_stack=" +
                        (aggregate.Expansions == 0 ? "0" : ((double)aggregate.StackDepthSum / aggregate.Expansions)
                            .ToString("F3", CultureInfo.InvariantCulture))));
            }
            foreach (var pair in expansionStackHistogram.OrderBy(pair => pair.Key))
            {
                SiProfile.Write("EXPANSION_STACK_DEPTH", Common(),
                    ("stack_depth", SiProfile.Number(pair.Key)), ("count", SiProfile.Number(pair.Value)));
            }
            foreach (var pair in expansionRecursionHistogram.OrderBy(pair => pair.Key))
            {
                SiProfile.Write("EXPANSION_RECURSION_DEPTH", Common(),
                    ("rec_depth", SiProfile.Number(pair.Key)), ("count", SiProfile.Number(pair.Value)));
            }
            var pendingHelpers = deferredHelperIds.Except(expandedHelperIds).Count();
            var distinctDeferred = deferredHelperIds.Count;
            var survivalRate = distinctDeferred == 0 ? 0.0 :
                (double)deferredHelperIds.Intersect(expandedHelperIds).Count() / distinctDeferred;
            var averageHelperVc = helperExpanded == 0 ? 0.0 : (double)helperExpandedVc / helperExpanded;
            SiProfile.Write("BITWISE_SUMMARY",
                Common(),
                ("result", outcome),
                ("helper_requested", SiProfile.Number(helperRequested)),
                ("helper_deferred", SiProfile.Number(helperDeferred)),
                ("helper_expanded", SiProfile.Number(helperExpanded)),
                ("helper_not_expanded", SiProfile.Number(pendingHelpers)),
                ("helper_vc_avoided", SiProfile.Number((long)Math.Round(averageHelperVc * pendingHelpers))),
                ("extra_over_queries", SiProfile.Number(extraOverQueries)),
                ("helper_survival_rate", SiProfile.Number(survivalRate)),
                ("details", outcome == "Correct" || outcome == "Errors"
                    ? "not_expanded=avoided before terminal result;vc_avoided=estimate from observed helper expansions"
                    : "not_expanded=pending at nonterminal stop;vc_avoided=estimate only"));
            SiProfile.Write("SI_SUMMARY",
                Common(),
                ("result", outcome),
                ("duration_ms", SiProfile.Ms(verificationClock.Elapsed)),
                ("under_checks", SiProfile.Number(underChecks)),
                ("over_checks", SiProfile.Number(overChecks)),
                ("other_checks", SiProfile.Number(otherChecks)),
                ("under_smt_ms", SiProfile.Number(underMilliseconds)),
                ("over_smt_ms", SiProfile.Number(overMilliseconds)),
                ("other_smt_ms", SiProfile.Number(otherMilliseconds)),
                ("max_under_ms", SiProfile.Number(maxUnderMilliseconds)),
                ("max_over_ms", SiProfile.Number(maxOverMilliseconds)),
                ("open_calls", SiProfile.Number(openCalls)),
                ("max_open_calls", SiProfile.Number(maxOpenCalls)),
                ("bound_blocked", SiProfile.Number(totalBlockedAtBound)),
                ("actual_expansions", SiProfile.Number(expansions)),
                ("fresh_vcs", SiProfile.Number(freshVcs)),
                ("di_merges", SiProfile.Number(diMerges)),
                ("vc_size", SiProfile.Number(vcSize)),
                ("max_stack_depth", SiProfile.Number(maxStackDepth)),
                ("max_rec_depth", SiProfile.Number(maxRecursionDepth)));
            SiProfile.SetSiContext("", "");
        }

        private (string key, string value) Common()
        {
            return ("implementation", implementation);
        }

        private static void Increment(Dictionary<int, long> histogram, int key)
        {
            histogram.TryGetValue(key, out var count);
            histogram[key] = count + 1;
        }

        private static string Histogram(IEnumerable<IGrouping<int, CallsitePoint>> groups)
        {
            return string.Join(",", groups.OrderBy(group => group.Key)
                .Select(group => group.Key + ":" + group.Count()));
        }
    }
}

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Channels;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Outcome = VC.VcOutcome;
using cba.Util;

namespace CoreLib
{
    public enum HydraReplayStepKind
    {
        Fresh,
        Merge
    }

    /// <summary>
    /// One deterministic SI/DI transition. MergeTargetPersistentId identifies
    /// the callsite that originally created the target VC; it is null for a
    /// fresh expansion. Ordered transitions reproduce the same DI DAG.
    /// </summary>
    public sealed class HydraReplayStep
    {
        public string CallSitePersistentId { get; init; }
        public HydraReplayStepKind Kind { get; init; }
        public string MergeTargetPersistentId { get; init; }
    }

    /// <summary>
    /// Replayable HYDRA partition: SI/DI expansion prefix + ancestor decisions.
    /// No raw Z3/solver state is serialized.
    /// </summary>
    public sealed class HydraPartition
    {
        public List<HydraReplayStep> ReplaySteps { get; init; } = new List<HydraReplayStep>();
        public List<HydraDecisionRecord> Decisions { get; init; } = new List<HydraDecisionRecord>();
        /// <summary>Split sites already used by ancestors; prevents infinite re-split after replay.</summary>
        public HashSet<string> PreviousSplitSites { get; init; } = new HashSet<string>();
        public int RecBound { get; init; } = 1;
        public int? PreferredWorker { get; init; }

        public HydraPartition Clone()
        {
            return new HydraPartition
            {
                ReplaySteps = ReplaySteps.Select(step => new HydraReplayStep
                {
                    CallSitePersistentId = step.CallSitePersistentId,
                    Kind = step.Kind,
                    MergeTargetPersistentId = step.MergeTargetPersistentId
                }).ToList(),
                Decisions = new List<HydraDecisionRecord>(Decisions),
                PreviousSplitSites = new HashSet<string>(PreviousSplitSites),
                RecBound = RecBound,
                PreferredWorker = PreferredWorker
            };
        }
    }

    public sealed class HydraDecisionRecord
    {
        public string CallSitePersistentId { get; init; }
        public StratifiedInlining.HydraDecisionType Type { get; init; }
    }

    public sealed class HydraParallelStats
    {
        public int PartitionsCreated;
        public int PartitionsSolved;
        public int StolenPartitions;
        public int ReconstructedPartitions;
        public int LocalSiblingReuse;
        public int Splits;
        public int PublishedSiblings;
        public int PublicationDeclined;
        public int PeakWorkers;
        public long WallMs;
        public int ExpansionAttempts;
        public int FreshStratifiedVCs;
        public int SuccessfulDiMerges;
        public int RejectedDiMergeCandidates;
        public int SolverCalls;
        public long CumulativeSmtTicks;
        public int RecursionBoundPartitions;
        public int UnknownPartitions;
        public int OwnerDequeues;
        public int PrefixEarlierGuards;
        public int ErrorWitnesses;
        public int WitnessConfirmations;
        public int WitnessConfirmationFailures;
        public int WitnessReplaySteps;
        public int WitnessDecisions;
        // Aggregate Stopwatch ticks across all cold partition solves. These
        // values intentionally sum concurrent worker time and may exceed wall.
        public long CoordinatorCloneTicks;
        public long InitLockWaitTicks;
        public long WorkerCloneTicks;
        public long WorkerPrepareTicks;
        public long WorkerSiConstructionTicks;
        public long WorkerPreSearchTicks;
        public long CloseLockWaitTicks;
        public long WorkerCloseTicks;
    }

    internal sealed class HydraWorkItem
    {
        public HydraPartition Partition { get; }
        int claimed;

        public HydraWorkItem(HydraPartition partition)
        {
            Partition = partition;
        }

        public bool TryClaim()
        {
            return Interlocked.CompareExchange(ref claimed, 1, 0) == 0;
        }
    }

    public sealed class HydraSiblingReservation
    {
        readonly HydraWorkItem item;
        readonly System.Action onReclaimed;

        internal HydraSiblingReservation(HydraWorkItem item, System.Action onReclaimed)
        {
            this.item = item;
            this.onReclaimed = onReclaimed;
        }

        public bool TryReclaim()
        {
            if (!item.TryClaim())
                return false;
            onReclaimed();
            return true;
        }
    }

    /// <summary>
    /// Local multicore HYDRA coordinator.
    /// Each worker owns an independent StratifiedInlining + DI + prover, built from
    /// a print/parse snapshot of the seed program (same recipe as BoogieUtil.ReResolveInMem).
    /// </summary>
    public static class HydraParallel
    {
        // Boogie/Z3 prover factory is not safe for concurrent CreateProver.
        static readonly object ProverInitLock = new object();

        public static Outcome Run(
            Program seedProgram,
            Implementation entry,
            VerifierCallback callback,
            int workers,
            int recBound,
            CancellationToken cancellationToken,
            out HydraParallelStats stats,
            out HydraPartition errorWitness)
        {
            var localStats = new HydraParallelStats();
            stats = localStats;
            errorWitness = null;
            if (workers < 1) workers = 1;
            var sw = Stopwatch.StartNew();
            if (cancellationToken.IsCancellationRequested)
            {
                sw.Stop();
                localStats.WallMs = sw.ElapsedMilliseconds;
                return Outcome.Inconclusive;
            }

            // Snapshot the pristine seed once. Each cold partition reparses this
            // snapshot to obtain independent declarations, VC state, and prover state.
            Program snapshot;
            var coordinatorCloneStart = Stopwatch.GetTimestamp();
            try
            {
                snapshot = CloneProgram(seedProgram);
                localStats.CoordinatorCloneTicks =
                    Stopwatch.GetTimestamp() - coordinatorCloneStart;
            }
            catch (Exception ex)
            {
                throw new InternalError("HYDRA: failed to snapshot program for multicore: " + ex.Message);
            }
            if (cancellationToken.IsCancellationRequested)
            {
                sw.Stop();
                localStats.WallMs = sw.ElapsedMilliseconds;
                return Outcome.Inconclusive;
            }
            var entryName = entry.Name;

            using var cts = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
            var acct = new WorkAccounting();
            var gate = new object();
            var shared = new SharedResult();

            var channel = Channel.CreateUnbounded<HydraWorkItem>(new UnboundedChannelOptions
            {
                SingleReader = false,
                SingleWriter = false
            });

            Interlocked.Increment(ref acct.Pending);
            Interlocked.Increment(ref acct.Queued);
            Interlocked.Increment(ref localStats.PartitionsCreated);
            channel.Writer.TryWrite(new HydraWorkItem(new HydraPartition { RecBound = recBound }));

            var workerTasks = new Task[workers];
            for (int w = 0; w < workers; w++)
            {
                var workerId = w;
                workerTasks[w] = Task.Run(() =>
                {
                    WorkerLoop(workerId, snapshot, entryName, callback, recBound,
                        channel, cts, acct, gate, shared, localStats);
                });
            }

            try
            {
                Task.WaitAll(workerTasks);
            }
            catch (AggregateException ae)
            {
                shared.WorkerError = ae.Flatten().InnerException ?? ae;
            }

            lock (gate)
            {
                if (cancellationToken.IsCancellationRequested)
                    shared.Record(Outcome.Inconclusive);
            }

            sw.Stop();
            localStats.WallMs = sw.ElapsedMilliseconds;


            if (shared.WorkerError != null)
                throw new InternalError("HYDRA worker failed: " + shared.WorkerError);

            if (shared.GlobalOutcome == Outcome.Errors && shared.ErrorWitness == null)
                throw new InternalError("HYDRA worker reported Errors without a replay witness");
            errorWitness = shared.ErrorWitness?.Clone();

            // Fail closed: unfinished work must never become SAFE.
            if (Volatile.Read(ref acct.Pending) != 0 || Volatile.Read(ref acct.Active) != 0 ||
                Volatile.Read(ref acct.Queued) != 0)
                shared.Record(Outcome.Inconclusive);
            if (localStats.PartitionsSolved < localStats.PartitionsCreated &&
                shared.GlobalOutcome == Outcome.Correct)
                shared.Record(Outcome.Inconclusive);

            // UNKNOWN/error must never become SAFE
            if (shared.GlobalOutcome != Outcome.Correct && shared.GlobalOutcome != Outcome.Errors)
                return shared.GlobalOutcome;

            return shared.GlobalOutcome;
        }

        sealed class WorkAccounting
        {
            public int Pending;
            public int Active;
            public int Idle;
            public int Queued;
        }

        /// <summary>VerifierCallback that ignores CEX (workers report verdict only).</summary>
        sealed class DiscardingVerifierCallback : VerifierCallback
        {
            public DiscardingVerifierCallback() : base(CoreOptions.ProverWarnings.None) { }
            public override void OnCounterexample(Counterexample ce, string reason) { }
        }

        static HydraParallel()
        {
            Debug.Assert(MergeOutcome(Outcome.Inconclusive, Outcome.Correct) == Outcome.Inconclusive);
            Debug.Assert(MergeOutcome(Outcome.TimedOut, Outcome.Correct) == Outcome.TimedOut);
            Debug.Assert(MergeOutcome(Outcome.OutOfResource, Outcome.Correct) == Outcome.OutOfResource);
            Debug.Assert(MergeOutcome(Outcome.Correct, Outcome.Errors) == Outcome.Errors);
        }

        internal static Outcome MergeOutcome(Outcome current, Outcome next)
        {
            if (current == Outcome.Errors || next == Outcome.Correct)
                return current;
            if (next == Outcome.Errors || current == Outcome.Correct)
                return next;
            return OutcomePriority(next) > OutcomePriority(current) ? next : current;
        }

        static int OutcomePriority(Outcome outcome)
        {
            switch (outcome)
            {
                case Outcome.Errors:
                    return 100;
                case Outcome.SolverException:
                    return 60;
                case Outcome.OutOfMemory:
                    return 50;
                case Outcome.OutOfResource:
                    return 40;
                case Outcome.TimedOut:
                    return 30;
                case Outcome.Inconclusive:
                    return 20;
                case Outcome.Correct:
                    return 0;
                default:
                    return 10;
            }
        }


        sealed class SharedResult
        {
            public Outcome GlobalOutcome = Outcome.Correct;
            public Exception WorkerError;

            public HydraPartition ErrorWitness;
            // Aggregation is monotonic: a later SAFE partition cannot erase an
            // UNKNOWN, timeout, or resource failure from an earlier partition.
            public void Record(Outcome outcome)
            {
                GlobalOutcome = MergeOutcome(GlobalOutcome, outcome);
            }

        }

        static void MarkWorkerActive(WorkAccounting acct, HydraParallelStats stats)
        {
            var active = Interlocked.Increment(ref acct.Active);
            while (true)
            {
                var peak = Volatile.Read(ref stats.PeakWorkers);
                if (active <= peak ||
                    Interlocked.CompareExchange(ref stats.PeakWorkers, active, peak) == peak)
                    return;
            }
        }

        static void WorkerLoop(
            int workerId,
            Program snapshot,
            string entryName,
            VerifierCallback callback,
            int recBound,
            Channel<HydraWorkItem> channel,
            CancellationTokenSource cts,
            WorkAccounting acct,
            object gate,
            SharedResult shared,
            HydraParallelStats stats)
        {
            try
            {
                while (!cts.IsCancellationRequested)
                {
                    // Prefer draining the queue before declaring quiescence.
                    if (channel.Reader.TryRead(out var workItem))
                    {
                        if (!workItem.TryClaim())
                            continue;
                        Interlocked.Decrement(ref acct.Queued);
                        var partition = workItem.Partition;
                        MarkWorkerActive(acct, stats);
                        try
                        {
                            if (partition.PreferredWorker.HasValue)
                            {
                                if (partition.PreferredWorker.Value != workerId)
                                    Interlocked.Increment(ref stats.StolenPartitions);
                                else
                                    Interlocked.Increment(ref stats.OwnerDequeues);
                            }

                            if (partition.ReplaySteps.Count > 0 || partition.Decisions.Count > 0)
                                Interlocked.Increment(ref stats.ReconstructedPartitions);


                            var outcome = SolvePartition(
                                workerId, snapshot, entryName, callback, partition, recBound,
                                channel, cts, acct, stats, out var errorWitness);

                            lock (gate)
                            {
                                if (outcome == Outcome.Errors)
                                {
                                    if (errorWitness == null)
                                        throw new InternalError("HYDRA worker found Errors without a leaf witness");
                                    if (shared.ErrorWitness == null)
                                    {
                                        shared.ErrorWitness = errorWitness.Clone();
                                        stats.ErrorWitnesses++;
                                        stats.WitnessReplaySteps = errorWitness.ReplaySteps.Count;
                                        stats.WitnessDecisions = errorWitness.Decisions.Count;
                                    }
                                }
                                shared.Record(outcome);

                            MacroSI.PRINT_DETAIL(
                                "HYDRA worker {0}: replay={1} decisions={2} outcome={3}",
                                workerId, partition.ReplaySteps.Count, partition.Decisions.Count, outcome);
                                if (outcome == Outcome.Errors)
                                    cts.Cancel();
                            }
                        }
                        finally
                        {
                            Interlocked.Decrement(ref acct.Active);
                            Interlocked.Decrement(ref acct.Pending);
                            Interlocked.Increment(ref stats.PartitionsSolved);
                        }
                        continue;
                    }

                    // Pending is incremented before publication and includes active
                    // work, so reaching zero cannot race with a producer.
                    if (Volatile.Read(ref acct.Pending) == 0)
                    {
                        channel.Writer.TryComplete();
                        break;
                    }

                    Interlocked.Increment(ref acct.Idle);
                    try
                    {
                        Thread.Sleep(2);
                    }
                    finally
                    {
                        Interlocked.Decrement(ref acct.Idle);
                    }
                }
            }
            catch (OperationCanceledException) when (cts.IsCancellationRequested)
            {
            }
            catch (Exception ex)
            {
                lock (gate)
                {
                    shared.WorkerError = ex;
                    shared.Record(Outcome.Inconclusive);
                }
                cts.Cancel();
            }
        }

        static Outcome SolvePartition(
            int workerId,
            Program snapshot,
            string entryName,
            VerifierCallback callback,
            HydraPartition partition,
            int recBound,
            Channel<HydraWorkItem> channel,
            CancellationTokenSource cts,
            WorkAccounting acct,
            HydraParallelStats stats,
            out HydraPartition errorWitness)
        {
            errorWitness = null;
            // Fresh AST + SI + prover per partition solve.
            // Serialize prover creation: Boogie.ProverFactory / Z3 process start
            // is not concurrent-safe. Solving after construction is independent.
            StratifiedInlining si;
            Implementation entryClone;
            cts.Token.ThrowIfCancellationRequested();
            var initLockWaitStart = Stopwatch.GetTimestamp();
            lock (ProverInitLock)
            {
                Interlocked.Add(ref stats.InitLockWaitTicks,
                    Stopwatch.GetTimestamp() - initLockWaitStart);
                cts.Token.ThrowIfCancellationRequested();
                var phaseStart = Stopwatch.GetTimestamp();
                var prog = CloneProgram(snapshot);
                Interlocked.Add(ref stats.WorkerCloneTicks,
                    Stopwatch.GetTimestamp() - phaseStart);
                phaseStart = Stopwatch.GetTimestamp();
                BoogieVerify.PrepareHydraWorkerProgram(prog);
                Interlocked.Add(ref stats.WorkerPrepareTicks,
                    Stopwatch.GetTimestamp() - phaseStart);
                cts.Token.ThrowIfCancellationRequested();
                entryClone = prog.TopLevelDeclarations.OfType<Implementation>()
                    .First(i => i.Name == entryName);
                phaseStart = Stopwatch.GetTimestamp();
                si = new StratifiedInlining(prog, null, false, null);
                Interlocked.Add(ref stats.WorkerSiConstructionTicks,
                    Stopwatch.GetTimestamp() - phaseStart);
            }
            try
            {
                cts.Token.ThrowIfCancellationRequested();
                Func<HydraPartition, HydraSiblingReservation> publisher = sibling =>
                {
                    // Reserve the sole queued slot only when a worker is genuinely
                    // idle. CAS prevents concurrent splitters from building a cold
                    // backlog while the existing worker set is already occupied.
                    if (cts.IsCancellationRequested || Volatile.Read(ref acct.Idle) <= 0 ||
                        Interlocked.CompareExchange(ref acct.Queued, 1, 0) != 0)
                    {
                        Interlocked.Increment(ref stats.PublicationDeclined);
                        return null;
                    }

                    var item = new HydraWorkItem(sibling);
                    Interlocked.Increment(ref acct.Pending);
                    Interlocked.Increment(ref stats.PartitionsCreated);
                    Interlocked.Increment(ref stats.PublishedSiblings);
                    if (!channel.Writer.TryWrite(item))
                    {
                        Interlocked.Decrement(ref acct.Queued);
                        Interlocked.Decrement(ref acct.Pending);
                        Interlocked.Decrement(ref stats.PartitionsCreated);
                        Interlocked.Decrement(ref stats.PublishedSiblings);
                        throw new InternalError("HYDRA: scheduler closed while publishing a sibling");
                    }
                    return new HydraSiblingReservation(item, () =>
                    {
                        Interlocked.Decrement(ref acct.Queued);
                        Interlocked.Decrement(ref acct.Pending);
                        Interlocked.Increment(ref stats.PartitionsSolved);
                        Interlocked.Increment(ref stats.LocalSiblingReuse);
                    });
                };
                // Discard worker CEX traces: they are rooted in cloned programs and
                // poison Corral's loop-trace mapping / refinement. The worker returns
                // a replay witness; the untouched master produces the native CEX.
                var workerCb = new DiscardingVerifierCallback();
                var outcome = si.SolveHydraPartition(entryClone, workerCb, partition, recBound, workerId,
                    publisher,
                    () => Volatile.Read(ref acct.Idle) > 0 && Volatile.Read(ref acct.Queued) == 0,
                    stats,
                    cts.Token,
                    out errorWitness);
                if (outcome == Outcome.Inconclusive)
                {
                    if (si.ReachedRecursionBound)
                        Interlocked.Increment(ref stats.RecursionBoundPartitions);
                    else
                        Interlocked.Increment(ref stats.UnknownPartitions);
                }
                return outcome;
            }
            finally
            {
                Interlocked.Add(ref stats.ExpansionAttempts, si.stats.diExpansionAttempts);
                Interlocked.Add(ref stats.FreshStratifiedVCs, si.stats.diFreshStratifiedVCs);
                Interlocked.Add(ref stats.SuccessfulDiMerges, si.stats.diSuccessfulMerges);
                Interlocked.Add(ref stats.RejectedDiMergeCandidates,
                    si.stats.diRejectedMergeCandidates);
                Interlocked.Add(ref stats.SolverCalls, si.stats.calls);
                Interlocked.Add(ref stats.CumulativeSmtTicks, si.stats.time);
                Interlocked.Add(ref stats.PrefixEarlierGuards,
                    si.HydraPrefixEarlierGuards);

                var closeLockWaitStart = Stopwatch.GetTimestamp();
                lock (ProverInitLock)
                {
                    Interlocked.Add(ref stats.CloseLockWaitTicks,
                        Stopwatch.GetTimestamp() - closeLockWaitStart);
                    var closeStart = Stopwatch.GetTimestamp();
                    try
                    {
                        si.Close();
                    }
                    finally
                    {
                        Interlocked.Add(ref stats.WorkerCloseTicks,
                            Stopwatch.GetTimestamp() - closeStart);
                    }
                }
            }
        }

        /// <summary>
        /// Isolated program copy for HYDRA workers.
        ///
        /// Reparse and resolve the pristine pre-VCGen seed to break every AST link.
        /// A post-VCGen program is not a valid seed because it contains synthetic
        /// callsite functions and passification state that cannot be instrumented twice.
        /// </summary>
        public static Program CloneProgram(Program p)
        {
            var ret = BoogieUtil.ReResolveInMem(p);
            if (!ret.TopLevelDeclarations.OfType<Implementation>().Any())
                throw new InternalError("HYDRA: clone produced zero implementations");
            return ret;
        }
    }

    public partial class StratifiedInlining
    {
        readonly List<HydraReplayStep> hydraReplaySteps = new List<HydraReplayStep>();
        HashSet<StratifiedCallSite> hydraFinalOpenCallSites;
        int hydraUnexpandedWitnessCallSites;

        void ResetHydraReplay()
        {
            hydraReplaySteps.Clear();
        }

        string HydraVcOriginId(StratifiedVC vc)
        {
            if (vc == mainVC)
                return "$main";
            if (!attachedVCInv.TryGetValue(vc, out var origin))
                throw new InternalError("HYDRA replay target has no origin callsite");
            return GetPersistentID(origin);
        }

        void RecordHydraFresh(StratifiedCallSite scs)
        {
            hydraReplaySteps.Add(new HydraReplayStep
            {
                CallSitePersistentId = GetPersistentID(scs),
                Kind = HydraReplayStepKind.Fresh
            });
        }

        void RecordHydraMerge(StratifiedCallSite scs, StratifiedVC target)
        {
            hydraReplaySteps.Add(new HydraReplayStep
            {
                CallSitePersistentId = GetPersistentID(scs),
                Kind = HydraReplayStepKind.Merge,
                MergeTargetPersistentId = HydraVcOriginId(target)
            });
        }

        List<HydraReplayStep> CaptureReplaySteps()
        {
            return hydraReplaySteps.Select(step => new HydraReplayStep
            {
                CallSitePersistentId = step.CallSitePersistentId,
                Kind = step.Kind,
                MergeTargetPersistentId = step.MergeTargetPersistentId
            }).ToList();
        }

        HydraPartition CaptureHydraLeafWitness(
            HydraPartition basePartition,
            IEnumerable<HydraDecision> activeDecisions,
            HashSet<string> previousSplitSites,
            int recBound)
        {
            var witnessDecisions = new List<HydraDecisionRecord>();
            if (basePartition?.Decisions != null)
            {
                witnessDecisions.AddRange(basePartition.Decisions.Select(decision =>
                    new HydraDecisionRecord
                    {
                        CallSitePersistentId = decision.CallSitePersistentId,
                        Type = decision.Type
                    }));
            }

            foreach (var decision in activeDecisions)
            {
                witnessDecisions.Add(new HydraDecisionRecord
                {
                    CallSitePersistentId = GetPersistentID(decision.CallSite),
                    Type = decision.Type
                });
            }

            return new HydraPartition
            {
                ReplaySteps = CaptureReplaySteps(),
                Decisions = witnessDecisions,
                PreviousSplitSites = new HashSet<string>(previousSplitSites),
                RecBound = recBound
            };
        }

        /// <summary>
        /// Replay a HydraPartition on this SI instance and search, optionally
        /// publishing MUST_REACH siblings to the coordinator.
        /// </summary>
        public Outcome SolveHydraPartition(
            Implementation impl,
            VerifierCallback callback,
            HydraPartition partition,
            int recBound,
            int workerId,
            Func<HydraPartition, HydraSiblingReservation> publishSibling,
            Func<bool> shouldSplitAggressively,
            HydraParallelStats stats,
            CancellationToken ct,
            out HydraPartition errorWitness,
            bool confirmOnly = false)
        {
            var preSearchStart = Stopwatch.GetTimestamp();
            procsHitRecBound = new HashSet<string>();
            forceInlineProcs.UnionWith(program.TopLevelDeclarations.OfType<Implementation>()
                .Where(p => BoogieUtil.checkAttrExists(ForceInlineAttr, p.Attributes) ||
                            BoogieUtil.checkAttrExists(ForceInlineAttr, p.Proc.Attributes))
                .Select(p => p.Name));

            prover.Assert(VCExpressionGenerator.True, true);
            di = new DI(this, !BoogieVerify.options.useDI);

            var hydraBaseStackSize = this.stats.stacksize;
            Push();
            try
            {
                ResetHydraReplay();

            StratifiedVC svc = new StratifiedVC(implName2StratifiedInliningInfo[impl.Name], implementations);
            if (!di.disabled)
                this.stats.diFreshStratifiedVCs++;
            mainVC = svc;
            di.RegisterMain(svc);
            var openCallSites = new HashSet<StratifiedCallSite>(svc.CallSites);
            prover.Assert(svc.vcexpr, true);

            var reporter = new StratifiedInliningErrorReporter(callback, this, svc);

            // Replay the exact ordered SI/DI transition log. Fresh expansions
            // are forced fresh and merge steps name the already-created target.
            // Re-running DI's candidate search here would make reconstruction
            // depend on hash iteration and could produce a different DAG.
            foreach (var step in partition.ReplaySteps)
            {
                var matches = openCallSites
                    .Where(candidate => GetPersistentID(candidate) == step.CallSitePersistentId)
                    .ToList();
                if (matches.Count != 1)
                {
                    throw new InternalError(
                        "HYDRA: replay callsite is missing or ambiguous: " +
                        step.CallSitePersistentId);
                }

                var scs = matches[0];
                openCallSites.Remove(scs);
                if (step.Kind == HydraReplayStepKind.Fresh)
                {
                    var fresh = Expand(scs, null, true, true);
                    if (fresh == null)
                        throw new InternalError("HYDRA: forced fresh replay unexpectedly merged");
                    openCallSites.UnionWith(fresh.CallSites);
                    continue;
                }

                StratifiedVC target;
                if (step.MergeTargetPersistentId == "$main")
                {
                    target = mainVC;
                }
                else
                {
                    var targets = attachedVCInv
                        .Where(entry => GetPersistentID(entry.Value) == step.MergeTargetPersistentId)
                        .Select(entry => entry.Key)
                        .ToList();
                    if (targets.Count != 1)
                    {
                        throw new InternalError(
                            "HYDRA: merge target is missing or ambiguous: " +
                            step.MergeTargetPersistentId);
                    }
                    target = targets[0];
                }

                Merge(scs, target);
            }

            // Replay ancestor decisions
            foreach (var d in partition.Decisions)
            {
                var scs = FindCallSiteByPersistentId(d.CallSitePersistentId);
                if (scs == null)
                {
                    throw new InternalError("HYDRA: cannot replay decision for " + d.CallSitePersistentId);
                }
                if (d.Type == HydraDecisionType.MUST_AVOID)
                {
                    AssertMustAvoid(scs);
                    if (attachedVC.ContainsKey(scs))
                        ApplyHydraDecisionToDI(HydraDecisionType.MUST_AVOID, attachedVC[scs]);
                }
                else
                {
                    if (attachedVC.TryGetValue(scs, out var reachedVc))
                    {
                        ApplyHydraDecisionToDI(HydraDecisionType.MUST_REACH, reachedVc);
                        AssertMustReach(reachedVc, null);
                    }
                    else
                    {
                        throw new InternalError("HYDRA: MUST_REACH site was not expanded during replay");
                    }
                }
            }

            if (stats != null)
                Interlocked.Add(ref stats.WorkerPreSearchTicks,
                    Stopwatch.GetTimestamp() - preSearchStart);
            Outcome outcome;
            if (confirmOnly)
            {
                errorWitness = null;
                reporter.reportTraceIfNothingToExpand = true;
                while (true)
                {
                    ct.ThrowIfCancellationRequested();
                    foreach (var callSite in openCallSites)
                    {
                        if (HasExceededRecursionDepth(callSite, recBound) ||
                            (StackDepthBound > 0 && StackDepth(callSite) > StackDepthBound))
                        {
                            prover.Assert(callSite.callSiteExpr, false);
                            procsHitRecBound.Add(callSite.callSite.calleeName);
                        }
                    }

                    reporter.callSitesToExpand = new List<StratifiedCallSite>();
                    reporter.reportTrace = false;
                    outcome = CheckVC(reporter, ct);
                    hydraUnexpandedWitnessCallSites = reporter.callSitesToExpand?.Count ?? -1;
                    if (outcome != Outcome.Errors || hydraUnexpandedWitnessCallSites == 0)
                        break;

                    foreach (var callSite in reporter.callSitesToExpand)
                    {
                        openCallSites.Remove(callSite);
                        var expanded = Expand(callSite, null, true, false);
                        if (expanded != null)
                            openCallSites.UnionWith(expanded.CallSites);
                    }
                }
                reporter.reportTraceIfNothingToExpand = false;
            }
            else
            {
                outcome = HydraSequentialWithPublish(
                    openCallSites, reporter, recBound, workerId, partition,
                    publishSibling, shouldSplitAggressively, stats, ct,
                    out errorWitness);
            }
            hydraFinalOpenCallSites = new HashSet<StratifiedCallSite>(openCallSites);

            return outcome;
            }
            finally
            {
                // Never leak the outer job frame or nested partition frames into
                // a reused master after cancellation, replay, or solver failure.
                while (this.stats.stacksize > hydraBaseStackSize)
                    Pop();
            }
        }

        Outcome ConfirmHydraErrorWitness(
            Implementation impl,
            VerifierCallback callback,
            HydraPartition witness,
            CancellationToken cancellationToken,
            out HashSet<StratifiedCallSite> openCallSites,
            out int unexpandedCallSites)
        {
            var outcome = SolveHydraPartition(
                impl, callback, witness, witness.RecBound, -1,
                null, null, null, cancellationToken,
                out _, true);
            openCallSites = hydraFinalOpenCallSites == null
                ? new HashSet<StratifiedCallSite>()
                : new HashSet<StratifiedCallSite>(hydraFinalOpenCallSites);
            unexpandedCallSites = hydraUnexpandedWitnessCallSites;
            return outcome;
        }

        StratifiedCallSite FindCallSiteByPersistentId(string id)
        {
            var seen = new HashSet<StratifiedCallSite>();
            void consider(StratifiedCallSite scs)
            {
                if (scs != null) seen.Add(scs);
            }

            foreach (var scs in attachedVC.Keys) consider(scs);
            foreach (var scs in parent.Keys) consider(scs);
            foreach (var scs in parent.Values) consider(scs);
            if (mainVC != null)
                foreach (var scs in mainVC.CallSites) consider(scs);
            foreach (var vc in attachedVC.Values.Distinct())
                foreach (var scs in vc.CallSites) consider(scs);

            var matches = seen.Where(scs => GetPersistentID(scs) == id).ToList();
            if (matches.Count > 1)
                throw new InternalError("HYDRA: duplicate persistent callsite ID during replay: " + id);
            return matches.SingleOrDefault();
        }


        /// <summary>
        /// Sequential HYDRA with optional publish of MUST_REACH siblings.
        /// Originating worker keeps MUST_AVOID on its incremental prover;
        /// MUST_REACH is stealable. After MUST_AVOID is proved, this worker
        /// does not re-enter the unconstrained space (that was the multicore
        /// soundness bug).
        /// </summary>
        Outcome HydraSequentialWithPublish(
            HashSet<StratifiedCallSite> openCallSites,
            StratifiedInliningErrorReporter reporter,
            int recBound,
            int workerId,
            HydraPartition basePartition,
            Func<HydraPartition, HydraSiblingReservation> publishSibling,
            Func<bool> shouldSplitAggressively,
            HydraParallelStats stats,
            CancellationToken ct,
            out HydraPartition errorWitness)
        {
            errorWitness = null;
            if (publishSibling == null)
                return HydraSequential(openCallSites, reporter, recBound);

            Outcome outcome = Outcome.Inconclusive;
            reporter.reportTraceIfNothingToExpand = true;
            HydraSplits = 0;
            HydraPartitionsSolved = 0;
            ReachedRecursionBound = false;

            int treesize = 0;
            var backtrackingPoints = new Stack<SiState>();
            var decisions = new Stack<HydraDecision>();
            var prevMustAsserted = new Stack<List<Tuple<StratifiedVC, Block>>>();
            var previousSplitSites = new HashSet<string>(
                basePartition?.PreviousSplitSites ?? Enumerable.Empty<string>());
            // Parallel to decisions: true if MUST_REACH sibling was published for this frame.
            var publishedAtFrame = new Stack<HydraSiblingReservation>();
            // Cap splits in one solve to prevent partition explosion after replay.
            const int MaxSplitsPerSolve = 32;

            var PrevAsserted = new Func<HashSet<Tuple<StratifiedVC, Block>>>(() =>
            {
                var ret = new HashSet<Tuple<StratifiedVC, Block>>();
                prevMustAsserted.ToList().Iter(ls => ls.Iter(tup => ret.Add(tup)));
                return ret;
            });

            var reachedBound = false;

            while (true)
            {
                if (ct.IsCancellationRequested)
                {
                    outcome = Outcome.Inconclusive;
                    goto done;
                }

                var size = di.disabled ? attachedVC.Count : di.ComputeSize();
                // Match sequential HYDRA threshold; only slightly more aggressive when idle.
                var aggressive = shouldSplitAggressively == null || shouldSplitAggressively();
                var growthThreshold = aggressive ? 2 : 3;

                if (HydraSplits < MaxSplitsPerSolve &&
                    ((treesize == 0 && size > 2) || (treesize != 0 && size > treesize + growthThreshold)))
                {
                    var maxVc = SelectHydraSplitCandidate(
                        openCallSites, previousSplitSites, ct, out var maxVcScore);

                    if (maxVc != null && attachedVCInv.ContainsKey(maxVc))
                    {
                        var scs = attachedVCInv[maxVc];
                        previousSplitSites.Add(GetPersistentID(scs));
                        HydraSplits++;
                        Interlocked.Increment(ref stats.Splits);

                        var replaySteps = CaptureReplaySteps();

                        // Ancestor decisions already on this worker, plus MUST_REACH for the sibling.
                        var ancestorDecisions = new List<HydraDecisionRecord>();
                        if (basePartition?.Decisions != null)
                            ancestorDecisions.AddRange(basePartition.Decisions);
                        foreach (var d in decisions.Reverse())
                        {
                            ancestorDecisions.Add(new HydraDecisionRecord
                            {
                                CallSitePersistentId = GetPersistentID(d.CallSite),
                                Type = d.Type
                            });
                        }
                        ancestorDecisions.Add(new HydraDecisionRecord
                        {
                            CallSitePersistentId = GetPersistentID(scs),
                            Type = HydraDecisionType.MUST_REACH
                        });

                        var reachSibling = new HydraPartition
                        {
                            ReplaySteps = replaySteps,
                            Decisions = ancestorDecisions,
                            PreviousSplitSites = new HashSet<string>(previousSplitSites),
                            RecBound = recBound,
                            PreferredWorker = workerId
                        };

                        // Keep MUST_AVOID local. Publish MUST_REACH only when the
                        // coordinator has demand; otherwise flip it locally on unwind.
                        publishedAtFrame.Push(publishSibling(reachSibling));

                        Push();
                        backtrackingPoints.Push(SiState.SaveState(this, openCallSites, previousSplitSites));
                        prevMustAsserted.Push(new List<Tuple<StratifiedVC, Block>>());
                        decisions.Push(new HydraDecision(HydraDecisionType.MUST_AVOID, 0, scs));
                        ApplyHydraDecisionToDI(HydraDecisionType.MUST_AVOID, maxVc);
                        AssertMustAvoid(scs);
                        treesize = di.disabled ? attachedVC.Count : di.ComputeSize();
                    }
                }

                foreach (StratifiedCallSite cs in openCallSites)
                {
                    if (HasExceededRecursionDepth(cs, recBound) ||
                        (StackDepthBound > 0 && StackDepth(cs) > StackDepthBound))
                    {
                        prover.Assert(cs.callSiteExpr, false);
                        procsHitRecBound.Add(cs.callSite.calleeName);
                        reachedBound = true;
                    }
                }

                reporter.callSitesToExpand = new List<StratifiedCallSite>();
                reporter.reportTrace = false;
                outcome = CheckVC(reporter, ct);

                MacroSI.PRINT_DETAIL(
                    "HYDRA worker {0} check: outcome={1} expand={2} decisions={3}",
                    workerId, outcome, reporter.callSitesToExpand?.Count ?? -1,
                    decisions.Count);
                if (outcome != Outcome.Correct && outcome != Outcome.Errors)
                    break;

                if (outcome == Outcome.Errors &&
                    (reporter.callSitesToExpand == null || reporter.callSitesToExpand.Count == 0))
                {
                    errorWitness = CaptureHydraLeafWitness(
                        basePartition, decisions.Reverse(), previousSplitSites, recBound);
                    HydraPartitionsSolved++;
                    break;
                }

                if (outcome == Outcome.Errors)
                {
                    foreach (var scs in reporter.callSitesToExpand)
                    {
                        openCallSites.Remove(scs);
                        var svc2 = Expand(scs, null, true, false);
                        if (svc2 != null) openCallSites.UnionWith(svc2.CallSites);
                    }
                    continue;
                }

                // outcome == Correct for the current leaf partition constraints.
                HydraPartitionsSolved++;

                // Backtrack. Frames with a published sibling do not flip locally
                // (the sibling owns MUST_REACH). Unwinding those frames is "done".
                while (true)
                {
                    if (decisions.Count == 0)
                    {
                        if (reachedBound)
                        {
                            outcome = Outcome.Inconclusive;
                            ReachedRecursionBound = true;
                        }
                        else
                        {
                            outcome = Outcome.Correct;
                        }
                        goto done;
                    }

                    var topDecision = decisions.Pop();
                    var topState = backtrackingPoints.Pop();
                    prevMustAsserted.Pop();
                    var siblingReservation = publishedAtFrame.Count > 0
                        ? publishedAtFrame.Pop() : null;
                    Pop(); // drop this frame's prover assertions

                    if (siblingReservation != null && topDecision.Flip == 0 &&
                        !siblingReservation.TryReclaim())
                    {
                        // MUST_AVOID child proved; MUST_REACH is (or was) in the queue.
                        // Continue unwinding or finish — do not flip, do not
                        // re-enter search without the remaining outer constraints.
                        // Outer frames remain on the prover stack after this Pop.
                        // Restore SI/DI bookkeeping for the outer frame.
                        topState.ApplyState(this, ref openCallSites, ref previousSplitSites);
                        if (decisions.Count == 0)
                        {
                            if (reachedBound)
                            {
                                outcome = Outcome.Inconclusive;
                                ReachedRecursionBound = true;
                            }
                            else
                                outcome = Outcome.Correct;
                            goto done;
                        }
                        // The current local leaf is complete. Continue unwinding
                        // published ancestors; re-entering the main loop here would
                        // overlap the stolen MUST_REACH partition.
                        continue;
                    }

                    // Sequential-style flip for non-published frames (shouldn't
                    // happen often in multicore path, but keep for completeness).
                    if (topDecision.Flip == 1)
                    {
                        // Already the second child; keep unwinding.
                        topState.ApplyState(this, ref openCallSites, ref previousSplitSites);
                        continue;
                    }

                    // Flip to the other child locally.
                    topState.ApplyState(this, ref openCallSites, ref previousSplitSites);
                    Push();
                    backtrackingPoints.Push(SiState.SaveState(this, openCallSites, previousSplitSites));
                    publishedAtFrame.Push(null);

                    if (topDecision.Type == HydraDecisionType.MUST_REACH)
                    {
                        AssertMustAvoid(topDecision.CallSite);
                        decisions.Push(new HydraDecision(HydraDecisionType.MUST_AVOID, 1, topDecision.CallSite));
                        if (attachedVC.ContainsKey(topDecision.CallSite))
                            ApplyHydraDecisionToDI(HydraDecisionType.MUST_AVOID, attachedVC[topDecision.CallSite]);
                        prevMustAsserted.Push(new List<Tuple<StratifiedVC, Block>>());
                    }
                    else
                    {
                        decisions.Push(new HydraDecision(HydraDecisionType.MUST_REACH, 1, topDecision.CallSite));
                        if (attachedVC.ContainsKey(topDecision.CallSite))
                        {
                            ApplyHydraDecisionToDI(HydraDecisionType.MUST_REACH, attachedVC[topDecision.CallSite]);
                            prevMustAsserted.Push(
                                AssertMustReach(attachedVC[topDecision.CallSite], PrevAsserted()));
                        }
                        else
                            prevMustAsserted.Push(new List<Tuple<StratifiedVC, Block>>());
                    }
                    treesize = di.disabled ? attachedVC.Count : di.ComputeSize();
                    break; // resume main loop under flipped child
                }
            }

        done:
            while (decisions.Count > 0)
            {
                Pop();
                decisions.Pop();
                if (backtrackingPoints.Count > 0) backtrackingPoints.Pop();
                if (prevMustAsserted.Count > 0) prevMustAsserted.Pop();
                if (publishedAtFrame.Count > 0) publishedAtFrame.Pop();
            }

            reporter.reportTraceIfNothingToExpand = false;
            return outcome;
        }
    }
}

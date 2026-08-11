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
using ProgTransformation;

namespace CoreLib
{
    /// <summary>
    /// Replayable HYDRA partition: SI/DI expansion prefix + ancestor decisions.
    /// No raw Z3/solver state is serialized.
    /// </summary>
    public sealed class HydraPartition
    {
        public HashSet<string> ExpansionPrefix { get; init; } = new HashSet<string>();
        public List<HydraDecisionRecord> Decisions { get; init; } = new List<HydraDecisionRecord>();
        /// <summary>Split sites already used by ancestors; prevents infinite re-split after replay.</summary>
        public HashSet<string> PreviousSplitSites { get; init; } = new HashSet<string>();
        public int RecBound { get; init; } = 1;
        public int? PreferredWorker { get; init; }

        public HydraPartition Clone()
        {
            return new HydraPartition
            {
                ExpansionPrefix = new HashSet<string>(ExpansionPrefix),
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
        public int PeakWorkers;
        public long WallMs;
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
            out HydraParallelStats stats)
        {
            var localStats = new HydraParallelStats();
            stats = localStats;
            if (workers < 1) workers = 1;

            var savedDI = BoogieVerify.options.useDI;
            var savedHydra = BoogieVerify.options.useHydra;
            var savedWorkers = BoogieVerify.options.hydraWorkers;
            BoogieVerify.options.useDI = true;
            // Workers call SolveHydraPartition; must not re-enter multicore.
            BoogieVerify.options.useHydra = false;
            BoogieVerify.options.hydraWorkers = 1;

            // Snapshot once with a deep AST copy. Mid-pipeline programs (post
            // loop-extract, pre-passify) often fail print/parse re-resolve; FixedDuplicator
            // + Resolve is the path used elsewhere in Corral (PersistentProgramDup).
            Program snapshot;
            try
            {
                snapshot = CloneProgram(seedProgram);
            }
            catch (Exception ex)
            {
                BoogieVerify.options.useDI = savedDI;
                BoogieVerify.options.useHydra = savedHydra;
                BoogieVerify.options.hydraWorkers = savedWorkers;
                throw new InternalError("HYDRA: failed to snapshot program for multicore: " + ex.Message);
            }
            var entryName = entry.Name;

            var sw = Stopwatch.StartNew();
            var cts = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
            var acct = new WorkAccounting();
            var gate = new object();
            var shared = new SharedResult();

            var channel = Channel.CreateUnbounded<HydraPartition>(new UnboundedChannelOptions
            {
                SingleReader = false,
                SingleWriter = false
            });

            Interlocked.Increment(ref acct.Pending);
            Interlocked.Increment(ref localStats.PartitionsCreated);
            channel.Writer.TryWrite(new HydraPartition { RecBound = recBound });

            localStats.PeakWorkers = workers;
            var workerTasks = new Task[workers];
            for (int w = 0; w < workers; w++)
            {
                var workerId = w;
                workerTasks[w] = Task.Run(() =>
                {
                    WorkerLoop(workerId, snapshot, entryName, callback, recBound,
                        channel, cts, acct, gate, shared, localStats);
                }, cts.Token);
            }

            try
            {
                Task.WaitAll(workerTasks);
            }
            catch (AggregateException ae)
            {
                shared.WorkerError = ae.Flatten().InnerException ?? ae;
            }

            sw.Stop();
            localStats.WallMs = sw.ElapsedMilliseconds;

            BoogieVerify.options.useDI = savedDI;
            BoogieVerify.options.useHydra = savedHydra;
            BoogieVerify.options.hydraWorkers = savedWorkers;

            if (shared.WorkerError != null)
                throw new InternalError("HYDRA worker failed: " + shared.WorkerError);

            // Fail closed: unfinished work must never become SAFE.
            if (Volatile.Read(ref acct.Pending) != 0 || Volatile.Read(ref acct.Active) != 0)
            {
                if (shared.GlobalOutcome != Outcome.Errors)
                    shared.GlobalOutcome = Outcome.Inconclusive;
            }
            if (localStats.PartitionsSolved < localStats.PartitionsCreated &&
                shared.GlobalOutcome == Outcome.Correct)
            {
                shared.GlobalOutcome = Outcome.Inconclusive;
            }

            // UNKNOWN/error must never become SAFE
            if (shared.GlobalOutcome != Outcome.Correct && shared.GlobalOutcome != Outcome.Errors)
                return shared.GlobalOutcome;

            return shared.GlobalOutcome;
        }

        sealed class WorkAccounting
        {
            public int Pending;
            public int Active;
        }

        /// <summary>VerifierCallback that ignores CEX (workers report verdict only).</summary>
        sealed class DiscardingVerifierCallback : VerifierCallback
        {
            public DiscardingVerifierCallback() : base(CoreOptions.ProverWarnings.None) { }
            public override void OnCounterexample(Counterexample ce, string reason) { }
        }


        sealed class SharedResult
        {
            public Outcome GlobalOutcome = Outcome.Correct;
            public Exception WorkerError;
        }

        static void WorkerLoop(
            int workerId,
            Program snapshot,
            string entryName,
            VerifierCallback callback,
            int recBound,
            Channel<HydraPartition> channel,
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
                    if (channel.Reader.TryRead(out var partition))
                    {
                        Interlocked.Increment(ref acct.Active);
                        try
                        {
                            if (partition.PreferredWorker.HasValue && partition.PreferredWorker.Value != workerId)
                                Interlocked.Increment(ref stats.StolenPartitions);

                            Interlocked.Increment(ref stats.ReconstructedPartitions);

                            var outcome = SolvePartition(
                                workerId, snapshot, entryName, callback, partition, recBound,
                                channel, cts, acct, stats);

                            lock (gate)
                            {
                                if (outcome == Outcome.Errors)
                                {
                                    shared.GlobalOutcome = Outcome.Errors;
                                    cts.Cancel();
                                }
                                else if (outcome == Outcome.Correct)
                                {
                                    if (shared.GlobalOutcome != Outcome.Errors)
                                        shared.GlobalOutcome = Outcome.Correct;
                                }
                                else
                                {
                                    if (shared.GlobalOutcome != Outcome.Errors)
                                        shared.GlobalOutcome = outcome;
                                    if (outcome == Outcome.TimedOut || outcome == Outcome.OutOfMemory)
                                        cts.Cancel();
                                }
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

                    // Queue empty. Quiescent only when nothing is pending or active.
                    if (Volatile.Read(ref acct.Pending) == 0 && Volatile.Read(ref acct.Active) == 0)
                    {
                        channel.Writer.TryComplete();
                        // Drain anything that raced in before complete.
                        if (channel.Reader.TryRead(out partition))
                        {
                            // Put pending back into accounting for this late item.
                            Interlocked.Increment(ref acct.Pending);
                            // Re-queue by processing path: push back via writer if possible.
                            if (!channel.Writer.TryWrite(partition))
                            {
                                // Writer closed: process inline.
                                Interlocked.Increment(ref acct.Active);
                                try
                                {
                                    var outcome = SolvePartition(
                                        workerId, snapshot, entryName, callback, partition, recBound,
                                        channel, cts, acct, stats);
                                    lock (gate)
                                    {
                                        if (outcome == Outcome.Errors)
                                        {
                                            shared.GlobalOutcome = Outcome.Errors;
                                            cts.Cancel();
                                        }
                                        else if (outcome != Outcome.Correct && shared.GlobalOutcome != Outcome.Errors)
                                            shared.GlobalOutcome = outcome;
                                    }
                                }
                                finally
                                {
                                    Interlocked.Decrement(ref acct.Active);
                                    Interlocked.Decrement(ref acct.Pending);
                                    Interlocked.Increment(ref stats.PartitionsSolved);
                                }
                            }
                            continue;
                        }
                        break;
                    }

                    if (channel.Reader.Completion.IsCompleted &&
                        Volatile.Read(ref acct.Pending) == 0 &&
                        Volatile.Read(ref acct.Active) == 0)
                        break;

                    Thread.Sleep(2);
                }
            }
            catch (OperationCanceledException)
            {
            }
            catch (Exception ex)
            {
                lock (gate)
                {
                    shared.WorkerError = ex;
                    if (shared.GlobalOutcome != Outcome.Errors)
                        shared.GlobalOutcome = Outcome.Inconclusive;
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
            Channel<HydraPartition> channel,
            CancellationTokenSource cts,
            WorkAccounting acct,
            HydraParallelStats stats)
        {
            // Fresh AST + SI + prover per partition solve.
            // Serialize prover creation: Boogie.ProverFactory / Z3 process start
            // is not concurrent-safe. Solving after construction is independent.
            StratifiedInlining si;
            Implementation entryClone;
            lock (ProverInitLock)
            {
                var prog = CloneProgram(snapshot);
                entryClone = prog.TopLevelDeclarations.OfType<Implementation>()
                    .First(i => i.Name == entryName);
                si = new StratifiedInlining(prog, null, false, null);
            }
            try
            {
                Action<HydraPartition> publisher = sibling =>
                {
                    Interlocked.Increment(ref acct.Pending);
                    Interlocked.Increment(ref stats.PartitionsCreated);
                    Interlocked.Increment(ref stats.Splits);
                    if (!channel.Writer.TryWrite(sibling))
                        Interlocked.Decrement(ref acct.Pending);
                };
                // Discard worker CEX traces: they are rooted in cloned programs and
                // poison Corral's loop-trace mapping / refinement. Verdict only;
                // real CEX is produced by sequential re-run on a clean clone.
                var workerCb = new DiscardingVerifierCallback();
                return si.SolveHydraPartition(entryClone, workerCb, partition, recBound, workerId,
                    publisher,
                    () => !channel.Reader.TryPeek(out _),
                    stats,
                    cts.Token);
            }
            finally
            {
                lock (ProverInitLock)
                {
                    si.Close();
                }
            }
        }

        /// <summary>
        /// Isolated program copy for HYDRA workers.
        ///
        /// FixedDuplicator(false) nulls CallCmd.Proc so Resolve rebinds callees inside
        /// the clone. We also must:
        ///   - deep-copy Procedure.Modifies (Procedure.Clone aliases the list; Boogie
        ///     3.5.6 ModSetCollector appends in place and would corrupt the seed);
        ///   - null GotoCmd.LabelTargets so Resolve rebuilds them from LabelNames
        ///     (otherwise successors still point at seed blocks and SIBoolControlVC
        ///     trace construction KeyNotFound-crashes / yields false bugs).
        /// </summary>
        public static Program CloneProgram(Program p)
        {
            var dup = new FixedDuplicator(/* retainProcCalls */ false);
            var ret = dup.VisitProgram(p);

            foreach (var proc in ret.TopLevelDeclarations.OfType<Procedure>())
            {
                if (proc.Modifies == null) continue;
                proc.Modifies = new List<IdentifierExpr>(
                    proc.Modifies.Select(ie => new IdentifierExpr(ie.tok, ie.Name)));
            }

            foreach (var impl in ret.TopLevelDeclarations.OfType<Implementation>())
            {
                if (impl.Blocks == null) continue;
                foreach (var block in impl.Blocks)
                {
                    if (block.TransferCmd is GotoCmd gc)
                    {
                        // Force Resolve to rebuild LabelTargets from LabelNames.
                        gc.LabelTargets = null;
                    }
                }
            }

            var err = BoogieUtil.ResolveProgram(ret);
            if (err != 0)
                throw new InternalError("HYDRA: failed to resolve cloned program (" + err + " errors)");
            err = BoogieUtil.TypecheckProgram(ret);
            if (err != 0)
                throw new InternalError("HYDRA: failed to typecheck cloned program (" + err + " errors)");
            if (!ret.TopLevelDeclarations.OfType<Implementation>().Any())
                throw new InternalError("HYDRA: clone produced zero implementations");
            return ret;
        }
    }

    public partial class StratifiedInlining
    {
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
            Action<HydraPartition> publishSibling,
            Func<bool> shouldSplitAggressively,
            HydraParallelStats stats,
            CancellationToken ct)
        {
            startTime = DateTime.UtcNow;
            procsHitRecBound = new HashSet<string>();
            forceInlineProcs.UnionWith(program.TopLevelDeclarations.OfType<Implementation>()
                .Where(p => BoogieUtil.checkAttrExists(ForceInlineAttr, p.Attributes) ||
                            BoogieUtil.checkAttrExists(ForceInlineAttr, p.Proc.Attributes))
                .Select(p => p.Name));

            prover.Assert(VCExpressionGenerator.True, true);
            di = new DI(this, !BoogieVerify.options.useDI);

            Push();

            StratifiedVC svc = new StratifiedVC(implName2StratifiedInliningInfo[impl.Name], implementations);
            mainVC = svc;
            di.RegisterMain(svc);
            var openCallSites = new HashSet<StratifiedCallSite>(svc.CallSites);
            prover.Assert(svc.vcexpr, true);

            var reporter = new StratifiedInliningErrorReporter(callback, this, svc);

            // Replay expansion prefix (persistent IDs), like CallTree repopulation.
            if (partition.ExpansionPrefix != null && partition.ExpansionPrefix.Count > 0)
            {
                while (true)
                {
                    var toAdd = new HashSet<StratifiedCallSite>();
                    var toRemove = new HashSet<StratifiedCallSite>();
                    foreach (var scs in openCallSites)
                    {
                        if (!partition.ExpansionPrefix.Contains(GetPersistentID(scs))) continue;
                        toRemove.Add(scs);
                        var ss = Expand(scs, null, true, true);
                        if (ss != null) toAdd.UnionWith(ss.CallSites);
                    }
                    openCallSites.ExceptWith(toRemove);
                    openCallSites.UnionWith(toAdd);
                    if (toRemove.Count == 0) break;
                }
            }

            // Replay ancestor decisions
            foreach (var d in partition.Decisions)
            {
                var scs = FindCallSiteByPersistentId(d.CallSitePersistentId);
                if (scs == null)
                {
                    // Decision refers to a site that should exist after prefix replay.
                    // Skip rather than crash; search remains sound over-approx if avoid
                    // is missing (may do extra work) but MUST_REACH missing would be
                    // incomplete — treat as error.
                    if (d.Type == HydraDecisionType.MUST_REACH)
                        throw new InternalError("HYDRA: cannot replay MUST_REACH for " + d.CallSitePersistentId);
                    continue;
                }
                if (d.Type == HydraDecisionType.MUST_AVOID)
                {
                    AssertMustAvoid(scs);
                    if (attachedVC.ContainsKey(scs))
                        ApplyHydraDecisionToDI(HydraDecisionType.MUST_AVOID, attachedVC[scs]);
                }
                else
                {
                    if (attachedVC.ContainsKey(scs))
                    {
                        ApplyHydraDecisionToDI(HydraDecisionType.MUST_REACH, attachedVC[scs]);
                        AssertMustReach(attachedVC[scs], null);
                    }
                    else
                    {
                        prover.Assert(scs.callSiteExpr, true);
                    }
                }
            }

            var outcome = HydraSequentialWithPublish(
                openCallSites, reporter, recBound, workerId, partition,
                publishSibling, shouldSplitAggressively, stats, ct);

            Pop();
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

            return seen.FirstOrDefault(scs => GetPersistentID(scs) == id);
        }

        HashSet<string> CaptureExpansionPrefix()
        {
            var ret = new HashSet<string>();
            foreach (var scs in attachedVC.Keys)
                ret.Add(GetPersistentID(scs));
            return ret;
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
            Action<HydraPartition> publishSibling,
            Func<bool> shouldSplitAggressively,
            HydraParallelStats stats,
            CancellationToken ct)
        {
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
            var publishedAtFrame = new Stack<bool>();
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
                    return Outcome.Inconclusive;

                if (BoogieUtil.BoogieOptions.TimeLimit != 0)
                {
                    if ((DateTime.UtcNow - startTime).TotalSeconds > BoogieUtil.BoogieOptions.TimeLimit)
                        return Outcome.TimedOut;
                }

                var size = di.disabled ? attachedVC.Count : di.ComputeSize();
                // Match sequential HYDRA threshold; only slightly more aggressive when idle.
                var aggressive = shouldSplitAggressively == null || shouldSplitAggressively();
                var growthThreshold = aggressive ? 2 : 3;

                if (HydraSplits < MaxSplitsPerSolve &&
                    ((treesize == 0 && size > 2) || (treesize != 0 && size > treesize + growthThreshold)))
                {
                    StratifiedVC maxVc = null;
                    int maxVcScore = -1;
                    if (!di.disabled)
                    {
                        var sizes = di.ComputeSubtrees();
                        var disj = di.ComputeNumDisjoint();
                        foreach (var vc in attachedVCInv.Keys.ToList())
                        {
                            if (!di.VcExists(vc)) continue;
                            if (!attachedVCInv.ContainsKey(vc)) continue;
                            var cs = attachedVCInv[vc];
                            if (previousSplitSites.Contains(GetPersistentID(cs))) continue;
                            var score = Math.Min(sizes[vc].Count, disj[vc]);
                            if (score >= maxVcScore)
                            {
                                maxVc = vc;
                                maxVcScore = score;
                            }
                        }
                    }

                    if (maxVc != null && attachedVCInv.ContainsKey(maxVc))
                    {
                        var scs = attachedVCInv[maxVc];
                        previousSplitSites.Add(GetPersistentID(scs));
                        HydraSplits++;

                        var prefix = CaptureExpansionPrefix();
                        if (basePartition?.ExpansionPrefix != null)
                            prefix.UnionWith(basePartition.ExpansionPrefix);

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
                            ExpansionPrefix = prefix,
                            Decisions = ancestorDecisions,
                            PreviousSplitSites = new HashSet<string>(previousSplitSites),
                            RecBound = recBound,
                            PreferredWorker = workerId
                        };

                        // Keep MUST_AVOID local (incremental prover); publish MUST_REACH.
                        publishSibling(reachSibling);
                        publishedAtFrame.Push(true);

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
                outcome = CheckVC(reporter);

                if (outcome != Outcome.Correct && outcome != Outcome.Errors)
                    break;

                if (outcome == Outcome.Errors &&
                    (reporter.callSitesToExpand == null || reporter.callSitesToExpand.Count == 0))
                {
                    HydraPartitionsSolved++;
                    break;
                }

                if (outcome == Outcome.Errors)
                {
                    foreach (var scs in reporter.callSitesToExpand)
                    {
                        openCallSites.Remove(scs);
                        var svc2 = Expand(scs, null, true, true);
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
                    var wasPublished = publishedAtFrame.Count > 0 && publishedAtFrame.Pop();
                    Pop(); // drop this frame's prover assertions

                    if (wasPublished && topDecision.Flip == 0)
                    {
                        // MUST_AVOID child proved; MUST_REACH is (or was) in the queue.
                        Interlocked.Increment(ref stats.LocalSiblingReuse);
                        // Continue unwinding or finish — do not flip, do not
                        // re-enter search without the remaining outer constraints.
                        // Outer frames remain on the prover stack after this Pop.
                        // Restore SI/DI bookkeeping for the outer frame.
                        topState.ApplyState(this, ref openCallSites, ref previousSplitSites);
                        // Keep searching under outer constraints (or finish if none).
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
                        // More outer MUST_AVOID frames still active — continue main loop.
                        break;
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
                    publishedAtFrame.Push(false);

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

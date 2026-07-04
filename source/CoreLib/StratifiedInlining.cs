using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Outcome = VC.VCGen.Outcome;
using cba.Util;
using Microsoft.Boogie.GraphUtil;

namespace CoreLib
{
    /****************************************
    *           Pseudo macros               *
    ****************************************/

    // TODO: replace this with conventional functions
    public class MacroSI
    {
        public static void PRINT(int lvl, string s, params object[] args)
        {
            if (StratifiedInlining.StratifiedInliningVerbose >= lvl)
                Console.WriteLine(s, args);
        }

        public static void PRINT(string s, params object[] args) { PRINT(0, s, args); }

        public static void PRINT_DETAIL(string s, params object[] args) { PRINT(1, s, args); }

        public static void PRINT_DEBUG(string s, params object[] args) { PRINT(2, s, args); }
    }

    /****************************************
    * Class for statistical analysis        *
    ****************************************/

    public class Stats
    {
        public int numInlined = 0;
        public int vcSize = 0;
        public int bck = 0;
        public int stacksize = 0;
        public int calls = 0;
        public long time = 0;

        public void print()
        {
            Console.WriteLine("--------- Stats ---------");
            Console.WriteLine("number of functions inlined: " + numInlined);
            Console.WriteLine("number of backtracking: " + bck);
            Console.WriteLine("total number of assertions in Z3 stack: " + stacksize);
            Console.WriteLine("total number of Z3 calls: " + calls);
            Console.WriteLine("total time spent in Z3: (tick) " + time);
            Console.WriteLine("-------------------------");
        }
    }


    /****************************************
    *          Stratified Inlining          *
    ****************************************/

    /* stratified inlining technique */
    public class StratifiedInlining : StratifiedVCGenBase
    {
        public static readonly string ForceInlineAttr = "ForceInline";
        public static int StratifiedInliningVerbose = 0;
        public static int StackDepthBound = 0;

        public Stats stats;

        /* call-site to VC map -- used for trace construction */
        public Dictionary<StratifiedCallSite, StratifiedVC> attachedVC;
        public Dictionary<StratifiedVC, StratifiedCallSite> attachedVCInv;

        /* VC of main */
        private StratifiedVC mainVC;

        /*  Parent linking -- used only for computing the recursion depth */
        public Dictionary<StratifiedCallSite, StratifiedCallSite> parent;

        // Set of implementations
        HashSet<string> implementations;

        /* Call Tree after VerifyImplementation */
        private HashSet<string> CallTree;

        /* extra Recursion bound */
        public Dictionary<string, int> extraRecBound;

        /* Procedures that hit the recursion bound */
        public HashSet<string> procsHitRecBound;

        /* Forced inline procs */
        HashSet<string> forceInlineProcs;

        // verification start time
        DateTime startTime;

        public HashSet<string> GetCallTree()
        {
            return CallTree;
        }

        public StratifiedInlining(Program program, string logFilePath, bool appendLogFile, Action<Implementation> PassiveImplInstrumentation) :
            base(program, logFilePath, appendLogFile, new List<Checker>(), PassiveImplInstrumentation)
        {
            stats = new Stats();

            this.extraRecBound = new Dictionary<string, int>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl =>
                {
                    var b = QKeyValue.FindIntAttribute(impl.Attributes, BoogieVerify.ExtraRecBoundAttr, -1);
                    if (b != -1) extraRecBound.Add(impl.Name, b);
                });

            attachedVC = new Dictionary<StratifiedCallSite, StratifiedVC>();
            attachedVCInv = new Dictionary<StratifiedVC, StratifiedCallSite>();
            parent = new Dictionary<StratifiedCallSite, StratifiedCallSite>();
            implementations = new HashSet<string>(implName2StratifiedInliningInfo.Keys);

            forceInlineProcs = new HashSet<string>();
        }

        /* depth in the call tree */
        public int StackDepth(StratifiedCallSite cs)
        {
            int i = 1;
            StratifiedCallSite iter = cs;
            while (parent.ContainsKey(iter))
            {
                iter = parent[iter]; /* previous callsite */
                i++;
            }
            return i;
        }

        /* depth of the recursion inlined so far */
        public int RecursionDepth(StratifiedCallSite cs)
        {
            int i = 1;
            StratifiedCallSite iter = cs;
            while (parent.ContainsKey(iter))
            {
                iter = parent[iter]; /* previous callsite */
                if (iter.callSite.calleeName == cs.callSite.calleeName)
                    i++; /* recursion */
            }
            return i;
        }

        /* Has this call-site reached the bound, given extraRecBound */
        public bool HasExceededRecursionDepth(StratifiedCallSite cs, int bound)
        {

            var i = RecursionDepth(cs);

            // Usual
            if (!extraRecBound.ContainsKey(cs.callSite.calleeName))
                return (i > bound);

            // Support extraRecBound
            return i > (bound + extraRecBound[cs.callSite.calleeName]);
        }

        /* for measuring Z3 stack */
        protected void Push()
        {
            stats.stacksize++;
            prover.Push();
        }

        /* for measuring Z3 stack */
        protected void Pop()
        {
            stats.stacksize--;
            prover.Pop();

        }

        public Outcome Fwd(HashSet<StratifiedCallSite> openCallSites, StratifiedInliningErrorReporter reporter, bool main, int recBound)
        {
            Outcome outcome = Outcome.Inconclusive;

            ForceInline(openCallSites, recBound);

            var boundHit = false;
            while (true)
            {
                // Check timeout
                if (CommandLineOptions.Clo.TimeLimit != 0)
                {
                    if ((DateTime.UtcNow - startTime).TotalSeconds > CommandLineOptions.Clo.TimeLimit)
                    {
                        return Outcome.TimedOut;
                    }
                }

                MacroSI.PRINT_DEBUG("  - underapprox");
                boundHit = false;

                // underapproximate query
                Push();


                foreach (StratifiedCallSite cs in openCallSites)
                {
                    prover.Assert(cs.callSiteExpr, false);
                }

                MacroSI.PRINT_DEBUG("    - check");
                reporter.reportTrace = main;
                outcome = CheckVC(reporter);
                Pop();
                MacroSI.PRINT_DEBUG("    - checked: " + outcome);
                if (outcome != Outcome.Correct) break;

                MacroSI.PRINT_DEBUG("  - overapprox");
                // overapproximate query
                Push();
                foreach (StratifiedCallSite cs in openCallSites)
                {
                    // Stop if we've reached the recursion bound or
                    // the stack-depth bound (if there is one)
                    if (HasExceededRecursionDepth(cs, recBound) ||
                        (StackDepthBound > 0 &&
                        StackDepth(cs) > StackDepthBound))
                    {
                        prover.Assert(cs.callSiteExpr, false);
                        procsHitRecBound.Add(cs.callSite.calleeName);
                        //Console.WriteLine("Proc {0} hit rec bound of {1}", cs.callSite.calleeName, recBound);
                        boundHit = true;
                    }
                }
                MacroSI.PRINT_DEBUG("    - check");
                reporter.reportTrace = false;
                reporter.callSitesToExpand = new List<StratifiedCallSite>();
                outcome = CheckVC(reporter);
                Pop();
                MacroSI.PRINT_DEBUG("    - checked: " + outcome);
                if (outcome != Outcome.Errors)
                {
                    if (boundHit && outcome == Outcome.Correct)
                        outcome = Outcome.ReachedBound;

                    break; // done
                }
                if (reporter.callSitesToExpand.Count == 0)
                    return Outcome.Inconclusive;

                var toExpand = reporter.callSitesToExpand;
                foreach (var scs in toExpand)
                {
                    openCallSites.Remove(scs);
                    var svc = Expand(scs);
                    if (svc != null)
                    {
                        openCallSites.UnionWith(svc.CallSites);
                    }
                }

                ForceInline(openCallSites, recBound);
            }
            return outcome;
        }

        void ForceInline(HashSet<StratifiedCallSite> openCallSites, int recBound)
        {
            do
            {
                // force inline
                var toExpand = new HashSet<StratifiedCallSite>(openCallSites.Where(cs => forceInlineProcs.Contains(cs.callSite.calleeName)));
                // filter away ones that have reached the bound
                toExpand.RemoveWhere(cs => HasExceededRecursionDepth(cs, recBound) ||
                        (StackDepthBound > 0 &&
                        StackDepth(cs) > StackDepthBound));
                if (toExpand.Count == 0) break;

                foreach (var scs in toExpand)
                {
                    openCallSites.Remove(scs);
                    var svc = Expand(scs);
                    if (svc != null)
                    {
                        openCallSites.UnionWith(svc.CallSites);
                    }
                }

            } while (true);
        }

        /* verification */
        public override Outcome VerifyImplementation(Implementation impl, VerifierCallback callback)
        {
            startTime = DateTime.UtcNow;

            procsHitRecBound = new HashSet<string>();

            // Find all procedures that are "forced inline"
            forceInlineProcs.UnionWith(program.TopLevelDeclarations.OfType<Implementation>()
                .Where(p => BoogieUtil.checkAttrExists(ForceInlineAttr, p.Attributes) || BoogieUtil.checkAttrExists(ForceInlineAttr, p.Proc.Attributes))
                .Select(p => p.Name));

            // assert true to flush all one-time axioms, decls, etc
            prover.Assert(VCExpressionGenerator.True, true);

            MacroSI.PRINT_DEBUG("Starting forward approach...");

            Push();

            StratifiedVC svc = new StratifiedVC(implName2StratifiedInliningInfo[impl.Name], implementations);
            mainVC = svc;
            HashSet<StratifiedCallSite> openCallSites = new HashSet<StratifiedCallSite>(svc.CallSites);
            prover.Assert(svc.vcexpr, true);

            Outcome outcome;
            var reporter = new StratifiedInliningErrorReporter(callback, this, svc);


            #region Eager inlining
            // Eager inlining 
            for (int i = 1; i < cba.Util.BoogieVerify.options.StratifiedInlining && openCallSites.Count > 0; i++)
            {
                var nextOpenCallSites = new HashSet<StratifiedCallSite>();
                foreach (StratifiedCallSite scs in openCallSites)
                {
                    if (HasExceededRecursionDepth(scs, CommandLineOptions.Clo.RecursionBound)) continue;

                    var ss = Expand(scs);
                    if (ss != null) nextOpenCallSites.UnionWith(ss.CallSites);
                }
                openCallSites = nextOpenCallSites;
            }
            #endregion

            #region Repopulate Call Tree
            if (cba.Util.BoogieVerify.options.CallTree != null)
            {
                while (true)
                {
                    var toAdd = new HashSet<StratifiedCallSite>();
                    var toRemove = new HashSet<StratifiedCallSite>();
                    foreach (StratifiedCallSite scs in openCallSites)
                    {
                        if (!cba.Util.BoogieVerify.options.CallTree.Contains(GetPersistentID(scs))) continue;
                        toRemove.Add(scs);
                        var ss = Expand(scs);
                        if (ss != null) toAdd.UnionWith(ss.CallSites);
                        MacroSI.PRINT_DETAIL(string.Format("Eagerly inlining: {0}", scs.callSite.calleeName), 2);
                    }
                    openCallSites.ExceptWith(toRemove);
                    openCallSites.UnionWith(toAdd);
                    if (toRemove.Count == 0) break;
                }
            }

            #endregion

            // Stratified Search
            int currRecursionBound = 1;
            while (true)
            {
                procsHitRecBound = new HashSet<string>();

                outcome = Fwd(openCallSites, reporter, true, currRecursionBound);

                // timeout?
                if (outcome == Outcome.Inconclusive || outcome == Outcome.OutOfMemory || outcome == Outcome.TimedOut)
                    break;

                // reached bound?
                if (outcome == Outcome.ReachedBound && currRecursionBound < CommandLineOptions.Clo.RecursionBound)
                {
                    if (StratifiedInliningVerbose > 0)
                        Console.WriteLine("SI: Exhausted recursion bound of {0}", currRecursionBound);
                    currRecursionBound++;
                    continue;
                }

                // outcome is either ReachedBound with currRecBound == Max or
                // Errors or Correct
                break;
            }

            Pop();

            if (StratifiedInliningVerbose > 1)
                stats.print();

            #region Stash call tree
            if (cba.Util.BoogieVerify.options.CallTree != null)
            {
                CallTree = new HashSet<string>();
                var callsites = new HashSet<StratifiedCallSite>();
                callsites.UnionWith(parent.Keys);
                callsites.UnionWith(parent.Values);
                callsites.ExceptWith(openCallSites);
                callsites.Iter(scs => CallTree.Add(GetPersistentID(scs)));
            }
            #endregion

            return outcome;
        }

        // Inline
        private StratifiedVC Expand(StratifiedCallSite scs)
        {
            return Expand(scs, null, true, false);
        }

        private StratifiedVC Expand(StratifiedCallSite scs, string name, bool DoSubst, bool dontMerge)
        {
            MacroSI.PRINT_DEBUG("    ~ extend callsite " + scs.callSite.calleeName);
            stats.numInlined++;
            var svc = new StratifiedVC(implName2StratifiedInliningInfo[scs.callSite.calleeName], implementations);

            foreach (var newCallSite in svc.CallSites)
            {
                parent[newCallSite] = scs;
            }
            VCExpr toassert;

            if (DoSubst)
                toassert = prover.VCExprGen.Implies(scs.callSiteExpr, scs.Attach(svc));
            else
                toassert = prover.VCExprGen.Implies(scs.callSiteExpr, prover.VCExprGen.And(
                svc.vcexpr, AttachByEquality(scs, svc)));

            prover.LogComment("Inlining " + scs.callSite.calleeName + " from " + (parent.ContainsKey(scs) ? attachedVC[parent[scs]].info.impl.Name : "main"));

            stats.vcSize += SizeComputingVisitor.ComputeSize(toassert);

            if (name != null)
                prover.AssertNamed(toassert, true, name);
            else
                prover.Assert(toassert, true);

            attachedVC[scs] = svc;
            attachedVCInv[svc] = scs;
            return svc;
        }

        // Return unique call ID of a call site
        private int GetSiCallId(StratifiedCallSite scs)
        {
            return QKeyValue.FindIntAttribute(scs.callSite.Attributes, "si_unique_call", -1);
        }

        // Get persistent ID of a callsite
        private string GetPersistentID(StratifiedCallSite scs)
        {
            if (!parent.ContainsKey(scs))
                return string.Format("{0}_131_{1}", scs.callSite.calleeName, GetSiCallId(scs));

            var ret = GetPersistentID(parent[scs]);
            return string.Format("{0}_262_{1}_393_{2}", ret, scs.callSite.calleeName, GetSiCallId(scs));
        }

        // Get persistent ID of a VC
        private string GetPersistentID(StratifiedVC vc)
        {
            var ret = "";
            if (attachedVCInv.ContainsKey(vc))
            {
                var scs = attachedVCInv[vc];
                ret = GetPersistentID(scs);
            }
            return string.Format("{0}_262_{1}", ret, vc.info.impl.Name);
        }

        // 'Attach' inlined from Boogie/StratifiedVC.cs (and made static)
        // TODO: add it to Boogie/StratifiedVC.cs
        // ---------------------------------------- 
        // Original Attach works with interface variables renaming. We don't want this, as we backtrack sometimes.
        // We add an equality clause instead.
        public static VCExpr AttachByEquality(StratifiedCallSite callee, StratifiedVC svcCallee)
        {
            System.Diagnostics.Contracts.Contract.Assert(callee.callSite.interfaceExprs.Count == svcCallee.interfaceExprVars.Count);
            StratifiedInliningInfo info = svcCallee.info;
            ProverInterface prover = info.vcgen.prover;
            VCExpressionGenerator gen = prover.VCExprGen;

            VCExpr conjunction = VCExpressionGenerator.True;

            for (int i = 0; i < svcCallee.interfaceExprVars.Count; i++)
            {
                /* interface variables */
                VCExpr equality = gen.Eq(svcCallee.interfaceExprVars[i], callee.interfaceExprs[i]);
                conjunction = gen.And(equality, conjunction);
            }

            return conjunction;
        }

        private Outcome CheckVC(ProverInterface.ErrorHandler reporter)
        {
            stats.calls++;
            var stopwatch = Stopwatch.StartNew();
            prover.Check();
            stats.time += stopwatch.ElapsedTicks;
            ProverInterface.Outcome outcome = prover.CheckOutcomeCore(reporter);
            return ConditionGeneration.ProverInterfaceOutcomeToConditionGenerationOutcome(outcome);
        }

        public override Outcome FindLeastToVerify(Implementation impl, ref HashSet<string> allBoolVars)
        {
            var name2VC = new Dictionary<string, StratifiedVC>();
            var getSVC = new Func<string, StratifiedVC>(name =>
                {
                    if (name2VC.ContainsKey(name))
                        return name2VC[name];
                    var tt = new StratifiedVC(implName2StratifiedInliningInfo[name], implementations);
                    name2VC.Add(name, tt);
                    return tt;
                });

            Push();

            StratifiedVC svc = getSVC(impl.Name);
            HashSet<StratifiedCallSite> openCallSites = new HashSet<StratifiedCallSite>(svc.CallSites);
            prover.Assert(svc.vcexpr, true);

            HashSet<StratifiedCallSite> nextOpenCallSites;
            while (openCallSites.Count != 0)
            {
                nextOpenCallSites = new HashSet<StratifiedCallSite>();
                foreach (StratifiedCallSite scs in openCallSites)
                {
                    svc = getSVC(scs.callSite.calleeName);
                    foreach (var newCallSite in svc.CallSites)
                    {
                        nextOpenCallSites.Add(newCallSite);
                    }
                    var toassert = scs.Attach(svc);
                    toassert = prover.VCExprGen.Implies(scs.callSiteExpr, toassert);
                    prover.Assert(toassert, true);
                }
                openCallSites = nextOpenCallSites;
            }

            // Find all the boolean constants
            var allConsts = new HashSet<VCExprVar>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                var constant = decl as Constant;
                if (constant == null) continue;
                if (!allBoolVars.Contains(constant.Name)) continue;
                var v = prover.Context.BoogieExprTranslator.LookupVariable(constant);
                allConsts.Add(v);
            }

            // Now, lets start the algo
            var min = refinementLoop(new EmptyErrorReporter(), new HashSet<VCExprVar>(), allConsts, allConsts);

            var ret = new HashSet<string>();
            foreach (var v in min)
            {
                ret.Add(v.Name);
            }
            allBoolVars = ret;

            Pop();

            return Outcome.Correct;
        }

        private HashSet<VCExprVar> refinementLoop(ProverInterface.ErrorHandler reporter, HashSet<VCExprVar> trackedVars, HashSet<VCExprVar> trackedVarsUpperBound, HashSet<VCExprVar> allVars)
        {
            Debug.Assert(trackedVars.IsSubsetOf(trackedVarsUpperBound));

            // If we already know the fate of all vars, then we're done.
            if (trackedVars.Count == trackedVarsUpperBound.Count)
                return new HashSet<VCExprVar>(trackedVars);

            // See if we already have enough variables tracked
            var success = refinementLoopCheckPath(reporter, trackedVars, allVars);
            if (success)
            {
                // We have enough
                return new HashSet<VCExprVar>(trackedVars);
            }

            // If all that remains is 1 variable, then we know that we must track it
            if (trackedVars.Count + 1 == trackedVarsUpperBound.Count)
                return new HashSet<VCExprVar>(trackedVarsUpperBound);

            // Partition the remaining set of variables
            HashSet<VCExprVar> part1, part2;
            var temp = new HashSet<VCExprVar>(trackedVarsUpperBound);
            temp.ExceptWith(trackedVars);
            Partition<VCExprVar>(temp, out part1, out part2);

            // First half
            var fh = new HashSet<VCExprVar>(trackedVars); fh.UnionWith(part2);
            var s1 = refinementLoop(reporter, fh, trackedVarsUpperBound, allVars);

            var a = new HashSet<VCExprVar>(part1); a.IntersectWith(s1);
            var b = new HashSet<VCExprVar>(part1); b.ExceptWith(s1);
            var c = new HashSet<VCExprVar>(trackedVarsUpperBound); c.ExceptWith(b);
            a.UnionWith(trackedVars);

            // Second half
            return refinementLoop(reporter, a, c, allVars);
        }

        private bool refinementLoopCheckPath(ProverInterface.ErrorHandler reporter, HashSet<VCExprVar> varsToSet, HashSet<VCExprVar> allVars)
        {
            var assumptions = new List<VCExpr>();
            var query = new HashSet<string>();
            varsToSet.Iter(v => query.Add(v.Name));

            prover.LogComment("FindLeast: Query Begin");

            foreach (var c in allVars)
            {
                if (varsToSet.Contains(c))
                {
                    assumptions.Add(c);
                }
                else
                {
                    assumptions.Add(prover.VCExprGen.Not(c));
                }
            }

            var o = CheckAssumptions(reporter, assumptions);
            if (o != Outcome.Correct && o != Outcome.Errors)
                throw new cba.Util.InternalError(string.Format("z3 ran out of resources in RefinementLoop: {0}", o));
            prover.LogComment("FindLeast: Query End");

            return (o == Outcome.Correct);
        }

        private Outcome CheckAssumptions(ProverInterface.ErrorHandler reporter, List<VCExpr> assumptions)
        {
            if (assumptions.Count == 0)
            {
                return CheckVC(reporter);
            }

            Push();
            foreach (var a in assumptions)
            {
                prover.Assert(a, true);
            }
            Outcome ret = CheckVC(reporter);
            Pop();
            return ret;
        }

        private static void Partition<T>(HashSet<T> values, out HashSet<T> part1, out HashSet<T> part2)
        {
            part1 = new HashSet<T>();
            part2 = new HashSet<T>();
            var size = values.Count;
            var crossed = false;
            var curr = 0;
            foreach (var s in values)
            {
                if (crossed) part2.Add(s);
                else part1.Add(s);
                curr++;
                if (!crossed && curr >= size / 2) crossed = true;
            }
        }
    }

    /****************************************
    *      Counter-example Generation       *
    ****************************************/

    public class EmptyErrorReporter : ProverInterface.ErrorHandler
    {
        public override void OnModel(IList<string> labels, Model model, ProverInterface.Outcome proverOutcome) { }
    }

    public class InsufficientDetailsToConstructCexPath : Exception
    {
        public InsufficientDetailsToConstructCexPath(string msg) : base(msg) { }

    }

    public class StratifiedInliningErrorReporter : ProverInterface.ErrorHandler
    {
        StratifiedInlining si;
        public VerifierCallback callback;
        StratifiedVC mainVC;
        public static TimeSpan ttime = TimeSpan.Zero;

        public bool reportTrace;
        public bool reportTraceIfNothingToExpand;

        public List<StratifiedCallSite> callSitesToExpand;
        List<Tuple<int, int>> orderedStateIds;

        public StratifiedInliningErrorReporter(VerifierCallback callback, StratifiedInlining si, StratifiedVC mainVC)
        {
            this.callback = callback;
            this.si = si;
            this.mainVC = mainVC;
            this.reportTrace = false;
            this.reportTraceIfNothingToExpand = false;
        }

        public override int StartingProcId()
        {
            return mainVC.id;
        }

        private Absy Label2Absy(string procName, string label)
        {
            int id = int.Parse(label);
            var l2a = si.implName2StratifiedInliningInfo[procName].label2absy;
            return (Absy)l2a[id];
        }

        public override void OnProverError(string message)
        {
            // Panic, shutdown!
            Console.WriteLine("Corral encountered a prover error. Giving up.");
            Console.Out.Flush();

            // Give a few seconds to the prover to shutdown
            var t1 =
            System.Threading.Tasks.Task.Run(async () =>
            {
                await System.Threading.Tasks.Task.Delay(5 * 1000);
                Environment.Exit(-1);
            });

            var t2 =
                System.Threading.Tasks.Task.Run(() => { si.prover.Close(); });

            System.Threading.Tasks.Task.WaitAll(t1, t2);
        }

        public override void OnModel(IList<string> labels, Model model, ProverInterface.Outcome proverOutcome)
        {
            // Timeout?
            if (proverOutcome != ProverInterface.Outcome.Invalid)
                return;

            var start = DateTime.Now;
            List<Absy> absyList = GetAbsyTrace(mainVC, labels);
            orderedStateIds = new List<Tuple<int, int>>();

            var cex = NewTrace(mainVC, absyList, model);
            //cex.PrintModel();

            if (StratifiedInlining.StratifiedInliningVerbose > 2)
                cex.Print(6, Console.Out);

            if (cex != null && (reportTrace ||
                (reportTraceIfNothingToExpand && callSitesToExpand.Count == 0)))
            {
                callback.OnCounterexample(cex, null);
                //this.PrintModel(model);
            }
            ttime += (DateTime.Now - start);
        }

        // returns a list of blocks followed by a fake assert
        private List<Absy> GetAbsyTrace(StratifiedVC svc, IList<string> labels)
        {
            if (CommandLineOptions.Clo.SIBoolControlVC)
                return GetAbsyTraceBoolControlVC(svc);
            else
                return GetAbsyTraceControlFlowVariable(svc, labels);
        }

        private List<Absy> GetAbsyTraceControlFlowVariable(StratifiedVC svc, IList<string> labels)
        {
            if (labels == null)
            {
                labels = si.prover.CalculatePath(svc.id);
            }
            var ret = new List<Absy>();
            foreach (var label in labels)
            {
                ret.Add(Label2Absy(svc.info.impl.Name, label));
            }
            return ret;
        }

        private List<Absy> GetAbsyTraceBoolControlVC(StratifiedVC svc)
        {
            Debug.Assert(CommandLineOptions.Clo.UseProverEvaluate, "Must use prover evaluate option with boolControlVC");

            var ret = new List<Absy>();
            var impl = svc.info.impl;
            var block = impl.Blocks[0];

            while (true)
            {
                ret.Add(block);
                var gc = block.TransferCmd as GotoCmd;
                if (gc == null) break;
                Block next = null;
                foreach (var succ in gc.labelTargets)
                {
                    var succtaken = (bool)svc.info.vcgen.prover.Evaluate(svc.blockToControlVar[succ]);
                    if (succtaken)
                    {
                        next = succ;
                        break;
                    }
                }
                Debug.Assert(next != null, "Must find a successor");
                Debug.Assert(!ret.Contains(next), "CFG cannot be cyclic");
                block = next;
            }

            // fake assert
            ret.Add(new AssertCmd(Token.NoToken, Expr.True));

            return ret;
        }

        private Counterexample NewTrace(StratifiedVC svc, List<Absy> absyList, Model model)
        {
            // assume that the assertion is in the last place??
            AssertCmd assertCmd = (AssertCmd)absyList[absyList.Count - 1];
            List<Block> trace = new List<Block>();
            var calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
            for (int j = 0; j < absyList.Count - 1; j++)
            {
                Block b = (Block)absyList[j];
                trace.Add(b);
                if (svc.callSites.ContainsKey(b))
                {
                    foreach (StratifiedCallSite scs in svc.callSites[b])
                    {
                        if (!si.attachedVC.ContainsKey(scs))
                        {
                            if (callSitesToExpand == null)
                                callSitesToExpand = new List<StratifiedCallSite>();

                            callSitesToExpand.Add(scs);
                        }
                        else
                        {
                            List<Absy> calleeAbsyList = GetAbsyTrace(si.attachedVC[scs], null);
                            var calleeCounterexample = NewTrace(si.attachedVC[scs], calleeAbsyList, model);
                            calleeCounterexamples[new TraceLocation(trace.Count - 1, scs.callSite.numInstr)] =
                            new CalleeCounterexampleInfo(calleeCounterexample, new List<object>());
                        }
                    }
                }
                if (svc.recordProcCallSites.ContainsKey(b) && (model != null || CommandLineOptions.Clo.UseProverEvaluate))
                {
                    foreach (StratifiedCallSite scs in svc.recordProcCallSites[b])
                    {
                        var args = new List<object>();
                        foreach (VCExpr expr in scs.interfaceExprs)
                        {
                            if (model == null && CommandLineOptions.Clo.UseProverEvaluate)
                            {
                                args.Add(svc.info.vcgen.prover.Evaluate(expr));
                            }
                            else
                            {
                                if (expr is VCExprIntLit)
                                {
                                    args.Add(model.MkElement((expr as VCExprIntLit).Val.ToString()));
                                }
                                else if (expr == VCExpressionGenerator.True)
                                {
                                    args.Add(model.MkElement("true"));
                                }
                                else if (expr == VCExpressionGenerator.False)
                                {
                                    args.Add(model.MkElement("false"));
                                }
                                else if (expr is VCExprVar)
                                {
                                    var idExpr = expr as VCExprVar;
                                    var prover = svc.info.vcgen.prover;
                                    string name = prover.Context.Lookup(idExpr);
                                    Model.Func f = model.TryGetFunc(name);
                                    if (f != null)
                                    {
                                        var val = f.GetConstant();
                                        if (val is Model.DatatypeValue)
                                        {
                                            args.Add(GenerateTraceValue(val));
                                        }
                                        else
                                        {
                                            args.Add(val);
                                        }
                                    }
                                }
                                else
                                {
                                    Debug.Assert(false);
                                }
                            }
                        }
                        calleeCounterexamples[new TraceLocation(trace.Count - 1, scs.callSite.numInstr)] =
                            new CalleeCounterexampleInfo(null, args);
                    }
                }
            }

            Block lastBlock = (Block)absyList[absyList.Count - 2];
            Counterexample newCounterexample = VC.VCGen.AssertCmdToCounterexample(assertCmd, lastBlock.TransferCmd, trace, null, model, svc.info.mvInfo, si.prover.Context);
            newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
            return newCounterexample;
        }

        private String GenerateTraceValue(Model.Element element)
        {
            var str = new System.IO.StringWriter();
            if (element is Model.DatatypeValue)
            {
                var val = (Model.DatatypeValue)element;
                if (val.ConstructorName == "_" && val.Arguments[0].ToString() == "(as-array)")
                {
                    var parens = val.Arguments[1].ToString();
                    var func = element.Model.TryGetFunc(parens.Substring(1, parens.Length - 2));
                    if (func != null)
                    {
                        str.Write("{");
                        var appCount = 0;
                        foreach (var app in func.Apps)
                        {
                            if (appCount++ > 0)
                                str.Write(",");
                            str.Write("\"");
                            var argCount = 0;
                            foreach (var arg in app.Args)
                            {
                                if (argCount++ > 0)
                                    str.Write(",");
                                str.Write(GenerateTraceValue(arg));
                            }
                            str.Write("\":{0}", GenerateTraceValue(app.Result));
                        }
                        if (func.Else != null)
                        {
                            if (func.AppCount > 0)
                                str.Write(",");
                            str.Write("\"*\":{0}", GenerateTraceValue(func.Else));
                        }
                        str.Write("}");
                    }
                }
            }
            if (str.ToString() == "")
                str.Write(element.ToString().Replace(" ", "").Replace("(", "").Replace(")", ""));
            return str.ToString();
        }
    }

}

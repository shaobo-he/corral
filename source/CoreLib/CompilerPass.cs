using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;

namespace cba
{
    // A compiler pass can be instantiated multiple times, but each instance can be
    // used only once. The pass records (permanently) its input and output program.
    abstract public class CompilerPass : ProgTransformation.TransformationPass
    {
        public CompilerPass() : base() { }

        public PersistentCBAProgram getInput()
        {
            return input as PersistentCBAProgram;
        }

        public PersistentCBAProgram getOutput()
        {
            return output as PersistentCBAProgram;
        }

        abstract public CBAProgram runCBAPass(CBAProgram p);

        virtual public ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            throw new InternalError("Map back trace: not implemented for " + this.GetType().Name);
            //return trace;
        }

        public TimeSpan lastRun;

        //////////////////////////////////////////////
        // Private guys -- need not bother about these
        //////////////////////////////////////////////

        protected override Program getInput(ProgTransformation.PersistentProgram inp)
        {
            PersistentCBAProgram ap = inp as PersistentCBAProgram;
            Debug.Assert(ap != null);

            return ap.getCBAProgram();
        }

        protected override ProgTransformation.PersistentProgram recordOutput(Program p)
        {
            CBAProgram ap = p as CBAProgram;
            Debug.Assert(ap != null);

            return ap.getPersistentVersion();
        }



        public PersistentCBAProgram run(PersistentCBAProgram inp)
        {
            var time1 = DateTime.Now;
            ProgTransformation.PersistentProgram outp = run(inp as ProgTransformation.PersistentProgram);
            var ret = outp as PersistentCBAProgram;
            var time2 = DateTime.Now;

            lastRun = (time2 - time1);

            return ret;
        }

        protected override Program runPass(Program inp)
        {
            CBAProgram ap = inp as CBAProgram;
            Debug.Assert(ap != null);

            CBAProgram ret = runCBAPass(ap);

            return ret as Program;
        }

    }


    public static class LoopBound
    {
        // loop impl -> the impl that calls it
        static Dictionary<string, Implementation> loopCaller;
        // Call graph
        static Dictionary<string, HashSet<Implementation>> Succ;
        static Dictionary<string, HashSet<Implementation>> Pred;
        // Max bound
        static int maxBound = -1;
        // Time taken
        public static TimeSpan timeTaken = TimeSpan.Zero;
        // User Annotations
        static List<string> UserAnnotations = new List<string>();

        // Initialize statics
        private static void Initialize(List<string> Annotations)
        {
            loopCaller = new Dictionary<string, Implementation>();
            Succ = new Dictionary<string, HashSet<Implementation>>();
            Pred = new Dictionary<string, HashSet<Implementation>>();
            UserAnnotations = Annotations;
        }

        public static Dictionary<string, int> Compute(CBAProgram program, int max, List<string> Annotations, BoogieVerifyOptions options)
        {
            var loopBounds = new Dictionary<string, int>();

            Initialize(Annotations);
            maxBound = max;
            var start = DateTime.Now;

            // remove non-free ensures and requires
            program.TopLevelDeclarations.OfType<Procedure>()
                .Iter(proc => proc.Ensures = proc.Ensures.Filter(en => en.Free));
            program.TopLevelDeclarations.OfType<Procedure>()
                .Iter(proc => proc.Requires = proc.Requires.Filter(en => en.Free));
            // remove assertions
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl => impl.Blocks
                    .Iter(blk => blk.Cmds = blk.Cmds.Map(c =>
                        {
                            var ac = c as AssertCmd;
                            if (ac == null) return c;
                            return new AssumeCmd(ac.tok, /*ac.Expr*/ Expr.True, ac.Attributes);
                        })));
            // Call graph
            ComputeCallGraph(program);

            // Gather the set of implementations with "loop" inside their name
            var allLoopImpls = new List<Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl => { if (impl.Name.Contains("loop")) allLoopImpls.Add(impl); });

            // Prune to the right form
            var loopImpls = allLoopImpls.Filter(CheckImpl);

            #region Process user annotations

            // Include user anntations
            var allLoops = new HashSet<string>();
            loopImpls.Iter(impl => allLoops.Add(impl.Name));
            foreach (var sp in UserAnnotations
                .Where(s => s.StartsWith("LB:"))
                .Select(s => s.Split(':'))
                .Where(sp => sp.Length == 3))
            {
                // grab bound
                var bound = 0;
                if (!Int32.TryParse(sp[2], out bound))
                    continue;

                // grab proc
                if (!allLoops.Contains(sp[1]))
                    continue;

                loopBounds[sp[1]] = bound;
                Console.WriteLine("LB: Loop {0} requires minimum {1} iterations (annotated)", sp[1], bound);
            }
            loopImpls = loopImpls.Filter(impl => !loopBounds.ContainsKey(impl.Name));
            #endregion

            if (loopImpls.Count == 0)
                return loopBounds;

            // Prepare query
            var query = PrepareQuery(loopImpls, program);

            // Set general options
            BoogieVerify.options = options;
            BoogieVerify.PrintImplsBeingVerified = true;

            // Set rec. bound
            var oldBound = BoogieUtil.RecursionBound;
            BoogieUtil.RecursionBound = maxBound;

            // Query
            var allErrors = new List<BoogieErrorTrace>();
            BoogieVerify.Verify(query, out allErrors);
            foreach (var trace in allErrors)
            {
                var loopName = QKeyValue.FindStringAttribute(trace.impl.Attributes, "LB_Mapping");
                var bound = RecBound(loopName, trace.cex, trace.impl.Name);
                if (bound <= 1) continue;
                loopBounds.Add(loopName, bound);
                Console.WriteLine("LB: Loop {0} requires minimum {1} iterations", loopName, bound);
            }

            BoogieUtil.RecursionBound = oldBound;
            BoogieVerify.PrintImplsBeingVerified = false;
            timeTaken = (DateTime.Now - start);

            return loopBounds;
        }

        public static PersistentCBAProgram AddLoopBounds(PersistentCBAProgram program, Dictionary<string, int> extraRecBounds)
        {
            if (extraRecBounds.Count == 0 || extraRecBounds.All(tup => tup.Value == 0)) return program;

            var prog = program.getCBAProgram();
            AddLoopBounds(prog, extraRecBounds);
            return new PersistentCBAProgram(prog, prog.mainProcName, prog.contextBound);
        }

        public static void AddLoopBounds(Program program, Dictionary<string, int> extraRecBounds)
        {
            program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => extraRecBounds.ContainsKey(impl.Name))
                .Iter(impl => impl.AddAttribute(BoogieVerify.ExtraRecBoundAttr, Expr.Literal(extraRecBounds[impl.Name])));
        }

        private static int RecBound(string recFunc, Counterexample trace, string traceName)
        {
            var ret = 0;
            if (trace == null) return ret;
            if (recFunc == traceName)
                ret++;

            for (int numBlock = 0; numBlock < trace.Trace.Count; numBlock++)
            {
                Block b = trace.Trace[numBlock];
                for (int numInstr = 0; numInstr < b.Cmds.Count; numInstr++)
                {
                    Cmd c = b.Cmds[numInstr];
                    var loc = new TraceLocation(numBlock, numInstr);
                    if (trace.CalleeCounterexamples.ContainsKey(loc))
                    {
                        ret +=
                            RecBound(recFunc, trace.CalleeCounterexamples[loc].Counterexample,
                            (c as CallCmd).Proc.Name);
                    }
                }
            }
            return ret;
        }

        private static Program PrepareQuery(IEnumerable<Implementation> loopImpls, Program program)
        {
            // Sometimes loops have multiple backedges, hence multiple recursive calls: merge them
            loopImpls.Iter(impl => mergeRecCalls(impl));

            var dup = new FixedDuplicator(true);
            // Make copies of loopImpl procs
            var loopProcsCopy = new Dictionary<string, Procedure>();
            loopImpls
                .Iter(impl => loopProcsCopy.Add(impl.Name, dup.VisitProcedure(impl.Proc)));

            loopProcsCopy.Values.Iter(proc => proc.Name += "_PassiveCopy");

            // Make copies of the caller implementations
            var loopCallerImplCopy = new Dictionary<string, Implementation>();
            var loopCallerProcCopy = new Dictionary<string, Procedure>();

            loopImpls
                .Iter(impl => loopCallerImplCopy.Add(impl.Name, dup.VisitImplementation(loopCaller[impl.Name])));

            loopImpls
                .Iter(impl => loopCallerProcCopy.Add(impl.Name, dup.VisitProcedure(loopCaller[impl.Name].Proc)));

            loopCallerImplCopy
                .Iter(kvp => kvp.Value.Name += "_EntryCopy_" + kvp.Key);

            loopCallerProcCopy
                .Iter(kvp => kvp.Value.Name += "_EntryCopy_" + kvp.Key);

            loopCallerImplCopy
                .Iter(kvp => kvp.Value.Proc = loopCallerProcCopy[kvp.Key]);

            // Instrument callers
            foreach (var kvp in loopCallerImplCopy)
            {
                var impl = kvp.Value;

                var av = BoogieAstFactory.MkLocal("LoopBound_AssertVar", Microsoft.Boogie.Type.Bool);
                impl.LocVars.Add(av);

                // av := true
                var init = BoogieAstFactory.MkVarEqConst(av, true);
                var initCmds = new List<Cmd>();
                initCmds.Add(init);
                initCmds.AddRange(impl.Blocks[0].Cmds);
                impl.Blocks[0].Cmds = initCmds;

                // av := false
                foreach (var blk in impl.Blocks)
                {
                    var newCmds = new List<Cmd>();
                    for (int i = 0; i < blk.Cmds.Count; i++)
                    {
                        // disable assertions
                        if (blk.Cmds[i] is AssertCmd && !BoogieUtil.isAssertTrue(blk.Cmds[i]))
                        {
                            newCmds.Add(new AssumeCmd(Token.NoToken, (blk.Cmds[i] as AssertCmd).Expr));
                            continue;
                        }
                        var cc = blk.Cmds[i] as CallCmd;
                        if (cc != null && cc.callee == kvp.Key)
                        {
                            newCmds.Add(blk.Cmds[i]);
                            newCmds.Add(BoogieAstFactory.MkVarEqConst(av, false));
                        }
                        else if (cc != null && loopProcsCopy.ContainsKey(cc.callee))
                        {
                            var ncc = new CallCmd(cc.tok, loopProcsCopy[cc.callee].Name, cc.Ins, cc.Outs, cc.Attributes, cc.IsAsync);
                            ncc.Proc = loopProcsCopy[cc.callee];
                            newCmds.Add(ncc);
                        }
                        else
                        {
                            newCmds.Add(blk.Cmds[i]);
                        }
                    }
                    blk.Cmds = newCmds;
                }

                // assert av
                impl.Blocks
                    .Where(blk => blk.TransferCmd is ReturnCmd)
                    .Iter(blk => blk.Cmds.Add(new AssertCmd(Token.NoToken, Expr.Ident(av))));
            }

            // Prepare program
            var ret = new Program();
            program.TopLevelDeclarations
                .Where(decl => !(decl is Implementation))
                .Iter(decl => ret.AddTopLevelDeclaration(decl));

            loopProcsCopy.Values
                .Iter(decl => ret.AddTopLevelDeclaration(decl));

            loopCallerImplCopy.Values
                .Iter(decl => ret.AddTopLevelDeclaration(decl));

            loopCallerProcCopy.Values
                .Iter(decl => ret.AddTopLevelDeclaration(decl));

            loopImpls
                .Iter(impl => ret.AddTopLevelDeclaration(impl));

            loopCallerImplCopy.Values
                .Iter(impl => impl.AddAttribute("entrypoint"));

            // Store mapping: entrypoint -> loop
            loopImpls
                .Select(loop => Tuple.Create(loop, loopCallerImplCopy[loop.Name]))
                .Iter(tup => tup.Item2.AddAttribute("LB_Mapping", tup.Item1.Name));

            ret = BoogieUtil.ReResolveInMem(ret);

            return ret;
        }

        private static void ComputeCallGraph(Program program)
        {
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl =>
                {
                    Succ.Add(impl.Name, new HashSet<Implementation>());
                    Pred.Add(impl.Name, new HashSet<Implementation>());
                });

            var name2Impl = BoogieUtil.nameImplMapping(program);
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    foreach (var cmd in blk.Cmds.OfType<CallCmd>())
                    {
                        if (!Succ.ContainsKey(cmd.callee)) continue;
                        Succ[impl.Name].Add(name2Impl[cmd.callee]);
                        Pred[cmd.callee].Add(impl);
                    }
                }
            }
        }

        private static bool CheckImpl(Implementation impl)
        {
            var preds = new HashSet<Implementation>(Pred[impl.Name]);

            // recursive?
            if (!preds.Contains(impl))
                return false;

            preds.Remove(impl);

            // unique caller?
            if (preds.Count != 1)
                return false;

            // cannot be main

            loopCaller.Add(impl.Name, preds.First());

            return true;
        }


        // If the impl has multiple calls:
        //   "call foo(args); return;"
        // with the same args, then merge these calls into one
        public static string mergeRecCalls(Implementation impl)
        {
            // find the recursive calls
            var rBlocks = new List<Block>();
            foreach (var blk in impl.Blocks)
            {
                var rc =
                    blk.Cmds
                    .OfType<CallCmd>()
                    .Where(cc => cc.callee == impl.Name);
                if (!rc.Any()) continue;
                if (rc.Count() != 1) return null;

                // make sure recursive call is last in the block
                var rcall = rc.First();
                if (rcall != blk.Cmds.Last()) return null;

                // check return
                if (!(blk.TransferCmd is ReturnCmd)) return null;

                rBlocks.Add(blk);
            }

            if (rBlocks.Count <= 1) return null;

            // grab the rec calls
            var recCalls = new Dictionary<string, CallCmd>();
            rBlocks.Iter(blk => recCalls.Add(blk.Label, blk.Cmds.Last() as CallCmd));

            // prune attributes
            var origAttr = new Dictionary<string, QKeyValue>();
            recCalls.Iter(kvp => origAttr.Add(kvp.Key, kvp.Value.Attributes));

            recCalls.Values
                .Iter(cc => cc.Attributes = BoogieUtil.removeAttrs(new HashSet<string> { "si_unique_call", "si_old_unique_call" }, cc.Attributes));

            // check that all recursive calls have the same arguments

            // Check 1: ToString
            var callStr = new HashSet<string>();
            recCalls.Values
                .Iter(cc =>
                {
                    var str = new System.IO.StringWriter();
                    var tt = new TokenTextWriter(str, BoogieUtil.BoogieOptions);
                    cc.Emit(tt, 0);
                    tt.Close();
                    callStr.Add(str.ToString());
                    str.Close();
                });

            if (callStr.Count != 1)
            {
                // restore attributes
                recCalls
                    .Iter(kvp => kvp.Value.Attributes = origAttr[kvp.Key]);
                return null;
            }

            // Check 2: AST
            var rc1 = recCalls[recCalls.Keys.First()];
            if (
                recCalls.Values
                .Where(c => !IsSame(rc1, c))
                .Any())
            {
                // restore attributes
                recCalls
                    .Iter(kvp => kvp.Value.Attributes = origAttr[kvp.Key]);

                return null;
            }

            // Merge
            rc1.Attributes = origAttr[recCalls.Keys.First()];
            var nb = BoogieAstFactory.MkBlock(rc1);
            rBlocks.Iter(blk => blk.Cmds.Remove(blk.Cmds.Last()));
            rBlocks.Iter(blk =>
            {
                var gc = BoogieAstFactory.MkGotoCmd(nb.Label);
                gc.LabelTargets = new List<Block>();
                gc.LabelTargets.Add(nb);
                blk.TransferCmd = gc;
            });
            impl.Blocks.Add(nb);
            return nb.Label;
        }


        // check if two calls have the same arguments
        private static bool IsSame(CallCmd c1, CallCmd c2)
        {
            if (c1.Ins.Count != c2.Ins.Count) return false;
            if (c1.Outs.Count != c2.Outs.Count) return false;
            if (c1.callee != c2.callee) return false;

            var op = c1.Outs.Zip(c2.Outs, (ie1, ie2) => (ie1.Decl.Name == ie2.Decl.Name));
            if (op.Any(b => b == false)) return false;

            var ins = c1.Ins.Zip(c2.Ins, (e1, e2) => Tuple.Create(e1, e2));
            foreach (var pair in ins)
            {
                var e1 = pair.Item1 as IdentifierExpr;
                var e2 = pair.Item2 as IdentifierExpr;

                // TODO: more deeper check
                if (e1 == null || e2 == null) return false;
                if (e1.Decl.Name != e2.Decl.Name) return false;
            }
            return true;
        }
    }


    // Do variable slicing on p 
    public class VariableSlicePass : CompilerPass
    {
        VariableSlicing vslice;
        ModifyTrans tinfo;

        public VariableSlicePass(VarSet v)
        {
            tinfo = new ModifyTrans();
            vslice = new VariableSlicing(v, tinfo);
            passName = "Variable Slicing";
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            // Type information is needed in some cases. For instance, the Command
            // Mem[x] := untracked-expr is converted to havoc temp; Mem[x] := temp. Here
            // we need the type of "untracked-expr" or of "Mem[x]"
            if (p.Typecheck(BoogieUtil.BoogieOptions) != 0)
            {
                p.Emit(new TokenTextWriter("error.bpl", BoogieUtil.BoogieOptions));
                throw new InternalError("Type errors");
            }
            vslice.VisitProgram(p as Program);
            BoogieUtil.DoModSetAnalysis(p);

            return p;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return tinfo.mapBackTrace(trace);
        }
    }


    // Does loop unrolling 
    public class LoopUnrollingPass : CompilerPass
    {
        // Number of times to unroll
        public int unrollNum { get; private set; }

        public LoopUnrollingPass(int n)
        {
            unrollNum = n;
            passName = "Loop Unrolling (" + unrollNum.ToString() + ")";
        }

        public override CBAProgram runCBAPass(CBAProgram inp)
        {
            if (unrollNum < 0)
            {
                return null;
            }
            else
            {
                inp.UnrollLoops(unrollNum, false);
            }

            return inp;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            if (unrollNum < 0)
            {
                return trace;
            }

            return undoUnrolling(trace);
        }

        public static ErrorTrace undoUnrolling(ErrorTrace trace)
        {

            // The heuristic used here is to get rid of the "#num" sign in the labels.
            // We assume that is the only way that Boogie.UnrollLoops changes the labels
            ErrorTrace ret = new ErrorTrace(trace.procName);

            for (int i = 0, n = trace.Blocks.Count; i < n; i++)
            {
                ret.addBlock(new ErrorTraceBlock(sanitizeLabel(trace.Blocks[i].blockName)));

                foreach (var c in trace.Blocks[i].Cmds)
                {
                    if (c is CallInstr)
                    {
                        var cc = c as CallInstr;
                        if (cc.calleeTrace != null)
                        {
                            ret.addInstr(new CallInstr(undoUnrolling(cc.calleeTrace), cc.asyncCall, cc.info));
                            continue;
                        }
                    }
                    ret.addInstr(c);
                }
            }
            if (trace.returns)
            {
                ret.addReturn();
            }

            return ret;
        }

        // Remove the "#num" from the end of lab, if there is something like this
        public static string sanitizeLabel(string lab)
        {
            if (!lab.Contains('#'))
                return lab;

            // Find the last occurrance of "#"
            int pos = lab.LastIndexOf('#');

            return lab.Substring(0, pos);
        }

    }

}

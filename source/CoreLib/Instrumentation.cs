using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;
// Contains classes that do program instrumentation

namespace cba
{
    // Instrumentation Config
    public static class InstrumentationConfig
    {
        // Print the instrumented bpl file
        public static bool printInstrumented = false;

        // Name of the instrumented bpl file to print
        public static string instrumentedFile = null;

        // Use old instrumentation where any context switch can raise exception
        public static bool UseOldInstrumentation = false;

        // Instrument RaiseException before all procedures
        public static bool raiseExceptionBeforeAllProcedures = false;

        // For debugging
        public static bool addRaiseException = true;

        // For debugging: 0 (None), 1 (Some), 2 (All)
        public static int addInvariants = 0;

        // Name of the procedure used to fix a context
        public static string corralFixContextName = "corral_fix_context";

        // Name of the procedure used to raiseException
        public static string corralFixRaiseExceptionName = "corral_fix_raise_exception";

        public static string getFixedContextProcName(int i)
        {
            return corralFixContextName + "_" + i.ToString();
        }

        public static CallCmd getFixedContextProc(int i)
        {
            var name = getFixedContextProcName(i);
            return new CallCmd(Token.NoToken, name, new List<Expr>(), new List<IdentifierExpr>());
        }

        public static int getFixedContextValue(Cmd c)
        {
            var cc = c as CallCmd;
            if (cc == null) return -1;
            var prefix = corralFixContextName + "_";
            if (cc.Proc.Name.StartsWith(prefix))
            {
                return Int32.Parse(cc.Proc.Name.Substring(prefix.Length));
            }
            else
            {
                return -1;
            }
        }

        public static string getFixedRaiseExceptionProcName()
        {
            return corralFixRaiseExceptionName;
        }

        public static CallCmd getFixedRaiseExceptionProc()
        {
            var name = getFixedRaiseExceptionProcName();
            return new CallCmd(Token.NoToken, name, new List<Expr>(), new List<IdentifierExpr>());
        }

        public static bool isFixedRaiseExceptionProc(Cmd c)
        {
            var cc = c as CallCmd;
            if (cc == null) return false;
            var prefix = corralFixContextName + "_";
            if (cc.Proc.Name == getFixedRaiseExceptionProcName())
            {
                return true;
            }
            else
            {
                return false;
            }
        }

        // Do a deterministic thread id assignment
        public static bool deterministicThreadId = false;

        /**
        * Normally, the sequentialization adds a context switch before every access to shared variables.
        * When /cooperative is given, this behaviour is suppressed.
        * context switches are only added where explictly specified by a dummy call to corral_yield. 
        **/
        public static bool cooperativeYield = false;

    }

    // This class massages call commands to a better form for the instrumenter.
    // Let g_i be global variables and l_i be local variables.
    // It replaces "call g_1 := foo(g_2,l_1)" with
    // l_2 := g_2;
    // call l_3 := foo(l_2, l_1);
    // g_1 := l_3;
    //
    // where l_2 and l_3 are new local variables.
    // The control flow of the program is not modified.
    public class RewriteCallCmds : FixedVisitor
    {
        // If onlyAsync is true, then only async calls are rewritten,
        // otherwise all calls are rewritten
        private bool onlyAsync;

        // A set of local variables that we may want to add to the current
        // implementation being visited. T
        private List<LocalVariable> localsToAdd;

        // A counter for generating local variables with different names
        private int localVarCount;

        // Name of the current implementation being visited
        private string implName;

        // The transformation carried out
        public ModifyTrans tinfo;

        // If onlyAsync is true, then only async calls are rewritten,
        // otherwise all calls are rewritten
        public RewriteCallCmds(bool a)
        {
            onlyAsync = a;
            localVarCount = 0;
            implName = null;
            tinfo = new ModifyTrans();
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            implName = node.Name;
            localsToAdd = new List<LocalVariable>();
            node = base.VisitImplementation(node);
            localsToAdd.Iterate(x => node.LocVars.Add((Variable)x));

            return node;
        }

        // Return a new local variable
        private LocalVariable getNewLocal(Microsoft.Boogie.Type type)
        {
            string name = "cmdloc_dummy_var_" + (localVarCount.ToString());
            TypedIdent tid = new TypedIdent(Token.NoToken, name, type);
            LocalVariable lv = new LocalVariable(Token.NoToken, tid);
            localsToAdd.Add(lv);
            localVarCount++;
            return lv;
        }

        // This is the main place where the rewriting happens
        public override Block VisitBlock(Block block)
        {
            GlobalVarsUsed usesg = new GlobalVarsUsed();

            // The new list of commands that we will construct
            List<Cmd> lcmds = new List<Cmd>();

            foreach (Cmd cmd in block.Cmds)
            {

                if (!(cmd is CallCmd))
                {
                    tinfo.add(implName, block.Label, new InstrTrans(cmd, cmd));
                    lcmds.Add(cmd);
                    continue;
                }

                CallCmd ccmd = cmd as CallCmd;

                // Ignore non-async calls if our flag says so
                if (onlyAsync && !ccmd.IsAsync)
                {
                    tinfo.add(implName, block.Label, new InstrTrans(cmd, cmd));
                    lcmds.Add(cmd);
                    continue;
                }


                // If the call command doesn't have any global variables, then no need
                // to instrument
                usesg.Visit(ccmd);
                if (usesg.Used.Count == 0)
                {
                    tinfo.add(implName, block.Label, new InstrTrans(cmd, cmd));
                    lcmds.Add(cmd);
                    continue;
                }

                // Get ready to instrument

                // The callee
                Procedure callee = ccmd.Proc;
                // This is the list of commands for saving the arguments
                List<Cmd> saveArgs = new List<Cmd>();
                // This is the new list of arguments
                List<Expr> newArgs = new List<Expr>();
                // This is the new list of returns
                List<IdentifierExpr> newReturns = new List<IdentifierExpr>();
                // This is the list of commands for restoring return values
                List<Cmd> restoreReturns = new List<Cmd>();

                // Go through the arguments of the call
                int argcount = 0;
                foreach (Expr exp in ccmd.Ins)
                {
                    if (exp != null)
                    {
                        usesg.reset();
                        usesg.Visit(exp);
                    }

                    if (exp != null && usesg.Used.Count != 0)
                    {
                        // Cannot use the following statement because
                        // exp.Type is not available unless type checking
                        // is performed. Let's avoid type checking for now.
                        //Variable lvar = getNewLocal(exp.Type);
                        Variable lvar = getNewLocal(ccmd.Proc.InParams[argcount].TypedIdent.Type);
                        saveArgs.Add(
                            BoogieAstFactory.MkVarEqExpr(lvar, exp)
                            );
                        newArgs.Add(Expr.Ident(lvar));
                    }
                    else
                    {
                        newArgs.Add(exp);
                    }
                    argcount++;
                }

                // Go through the return values
                argcount = 0;
                foreach (IdentifierExpr exp in ccmd.Outs)
                {
                    if (exp != null)
                    {
                        usesg.reset();
                        usesg.Visit(exp);
                    }

                    if (exp != null && usesg.Used.Count != 0)
                    {
                        Variable lvar = getNewLocal(ccmd.Proc.OutParams[argcount].TypedIdent.Type);
                        IdentifierExpr ret = new IdentifierExpr(Token.NoToken, lvar);
                        restoreReturns.Add(
                            BoogieAstFactory.MkVarEqExpr(exp.Decl, ret)
                            );
                        newReturns.Add(ret);
                    }
                    else
                    {
                        newReturns.Add(exp);
                    }
                    argcount++;
                }

                // Now add to lcmds: saveArgs; newcall command; restoreReturns
                var newCmds = new List<Cmd>();
                newCmds.AddRange(saveArgs);
                CallCmd newcallcmd = new CallCmd(ccmd.tok, ccmd.Proc.Name, newArgs, newReturns, ccmd.Attributes, ccmd.IsAsync);
                newcallcmd.Proc = callee; // Temporary hack to avoid doing "Resolve"

                newCmds.Add(newcallcmd);
                newCmds.AddRange(restoreReturns);

                tinfo.add(implName, block.Label, new InstrTrans(cmd, newCmds, saveArgs.Count));
                lcmds.AddRange(newCmds);
            }

            block.Cmds = lcmds;

            return block;
        }
    }

    public class AssertLocation : IEqualityComparer<AssertLocation>
    {
        public string procName;
        public string blockName;
        public int instrNo;

        public AssertLocation()
        {
            procName = blockName = null;
            instrNo = 0;
        }

        public AssertLocation(string procName, string blockName, int instrNo)
        {
            this.procName = procName;
            this.blockName = blockName;
            this.instrNo = instrNo;
        }

        public bool Equals(AssertLocation a, AssertLocation b)
        {
            return (a.procName == b.procName && a.blockName == b.blockName && a.instrNo == b.instrNo);
        }

        public int GetHashCode(AssertLocation a)
        {
            return 131 * a.procName.GetHashCode() + a.blockName.GetHashCode() + a.instrNo;
        }
    }

    // This class rewrites asserts.
    // It replaces "assert e" with:
    // goto lab1, lab2;
    // 
    // lab1:
    //   assume not(e)
    //   call cba_assert_not_reachable();
    //   //assume false;
    //   goto lab3;
    // lab2:
    //   assume e
    //   goto lab3;
    // lab3:
    //   ...
    public class RewriteAsserts
    {
        public static readonly string AssertIdentificationAttribute = "corral_assert_pt";

        // The transformation carried out
        HashSet<string> lab1BlocksAdded;
        HashSet<string> lab1BlocksAddedForReq;
        HashSet<string> lab1BlocksAddedForEns;
        HashSet<string> lab2BlocksAdded;
        HashSet<string> lab2BlocksAddedForReqEns;
        HashSet<string> lab3BlocksAdded;

        // new name count
        int newNameCount;

        // Set of all assert locations in the input program
        Dictionary<AssertLocation, bool> allAssertLocations;

        // Location of the failing assert in the trace given to mapBackTrace
        public AssertLocation failingAssert { get; private set; }

        // Found the assert?
        public bool assertFound
        {
            get
            {
                return (failingAssert != null);
            }
        }

        // Should we expect to find a failing assert in the trace?
        private bool shouldFindAssert;

        public RewriteAsserts()
        {
            lab1BlocksAdded = new HashSet<string>();
            lab1BlocksAddedForReq = new HashSet<string>();
            lab1BlocksAddedForEns = new HashSet<string>();
            lab2BlocksAdded = new HashSet<string>();
            lab2BlocksAddedForReqEns = new HashSet<string>();
            lab3BlocksAdded = new HashSet<string>();
            newNameCount = 0;
            allAssertLocations = new Dictionary<AssertLocation, bool>(new AssertLocation());
            failingAssert = null;
            shouldFindAssert = true;
        }

        public RewriteAsserts(bool shouldFindAssert)
            : this()
        {
            this.shouldFindAssert = shouldFindAssert;
        }

        // For allowing multiple traces to be mapped back
        public void reset()
        {
            failingAssert = null;
        }

        public Program VisitProgram(Program inp)
        {
            var hasDecl = false;

            foreach (var decl in inp.TopLevelDeclarations)
            {
                if (decl is Implementation)
                {
                    VisitImplementation(decl as Implementation);
                }
                else if (decl is Procedure)
                {
                    if ((decl as Procedure).Name == LanguageSemantics.assertNotReachableName())
                    {
                        hasDecl = true;
                    }
                }
            }

            if (!hasDecl)
            {
                inp.AddTopLevelDeclaration(
                    new Procedure(
                        Token.NoToken, LanguageSemantics.assertNotReachableName(),
                        new List<TypeVariable>(), new List<Variable>(), new List<Variable>(),
                        new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>()));

            }
            else
            {
                // Delete all annotations of corral_assert_not_reachable (otherwise we can get type errors)
                var assertProc = BoogieUtil.findProcedureDecl(inp.TopLevelDeclarations, LanguageSemantics.assertNotReachableName());
                assertProc.Modifies = new List<IdentifierExpr>();
                assertProc.Requires = new List<Requires>();
                assertProc.Ensures = new List<Ensures>();
            }

            // Make all requires and ensures free
            foreach (var proc in inp.TopLevelDeclarations.OfType<Procedure>())
            {
                // Make all requires free
                proc.Requires = new List<Requires>(proc.Requires.OfType<Requires>().Select(r => new Requires(r.tok, true, r.Condition, null, r.Attributes)).ToArray());
                // Make all ensures free
                proc.Ensures = new List<Ensures>(proc.Ensures.OfType<Ensures>().Select(r => new Ensures(r.tok, true, r.Condition, null, r.Attributes)).ToArray());
            }

            return inp;
        }

        private Implementation VisitImplementation(Implementation node)
        {
            var newBlocks = new List<Block>();

            foreach (Block block in node.Blocks)
            {
                var currCmds = new List<Cmd>();
                var currLabel = block.Label;

                foreach (Cmd cmd in block.Cmds)
                {
                    if (BoogieUtil.isAssertTrue(cmd))
                    {
                        // convert assert true to assume true
                        currCmds.Add(new AssumeCmd(cmd.tok, Expr.True));
                        continue;
                    }

                    if (cmd is AssertCmd)
                    {
                        branchForAssert((cmd as AssertCmd).Expr, ref currLabel, ref currCmds, newBlocks, 0);
                        continue;
                    }

                    // For a call, check for non-free requires 
                    if (cmd is CallCmd)
                    {
                        var ccmd = cmd as CallCmd;
                        var reqToAssert = ccmd.Proc.Requires.OfType<Requires>().Where(r => !r.Free);
                        if (reqToAssert.Count() == 0)
                        {
                            currCmds.Add(cmd);
                            continue;
                        }
                        var formalToActual = new Dictionary<string, Expr>();
                        for (int i = 0; i < ccmd.Ins.Count; i++)
                            formalToActual.Add(ccmd.Proc.InParams[i].Name, ccmd.Ins[i]);

                        var subst = new Substitution(v =>
                        {
                            if (formalToActual.ContainsKey(v.Name)) return formalToActual[v.Name];
                            return Expr.Ident(v);
                        });

                        Expr aexpr = Expr.True;
                        foreach (var req in reqToAssert)
                            aexpr = Expr.And(aexpr, Substituter.Apply(subst, req.Condition));

                        branchForAssert(aexpr, ref currLabel, ref currCmds, newBlocks, 1);

                        currCmds.Add(cmd);
                        continue;
                    }

                    currCmds.Add(cmd);
                }

                // At a return, check for non-free ensures
                if (block.TransferCmd is ReturnCmd)
                {
                    var ensToAssert = node.Proc.Ensures.OfType<Ensures>().Where(e => !e.Free);
                    if (ensToAssert.Count() != 0)
                    {
                        Expr aexpr = Expr.True;
                        foreach (var ens in ensToAssert)
                            aexpr = Expr.And(aexpr, ens.Condition);

                        branchForAssert(aexpr, ref currLabel, ref currCmds, newBlocks, 2);
                    }
                }

                newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds, block.TransferCmd));
            }

            node.Blocks = newBlocks;

            foreach (var block in newBlocks)
            {
                recordNotReachableProcLocation(node.Name, block);
            }

            return node;
        }

        // forAssert: 0 for assert, 1 for requires, 2 for ensures
        private void branchForAssert(Expr aexpr, ref string currLabel, ref List<Cmd> currCmds, List<Block> newBlocks, int forAssert)
        {
            var acallcmd = new CallCmd(Token.NoToken, LanguageSemantics.assertNotReachableName(), new List<Expr>(), new List<IdentifierExpr>());

            var lab1 = getNewLabel();
            var lab2 = getNewLabel();
            var lab3 = getNewLabel();

            lab1BlocksAdded.Add(lab1);
            lab2BlocksAdded.Add(lab2);
            lab3BlocksAdded.Add(lab3);

            if (forAssert != 0) lab2BlocksAddedForReqEns.Add(lab2);
            if (forAssert == 1) lab1BlocksAddedForReq.Add(lab1);
            if (forAssert == 2) lab1BlocksAddedForEns.Add(lab1);

            // End current block
            newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds, BoogieAstFactory.MkGotoCmd(lab1, lab2)));

            // lab1
            currLabel = lab1;
            currCmds = new List<Cmd>();

            currCmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(aexpr),
                new QKeyValue(Token.NoToken, AssertIdentificationAttribute, new List<object>(), null)));
            currCmds.Add(acallcmd);
            // cannot put assume false here: when the assert is inside
            // an atomic block then a context switch would not happen between
            // the assert and this assume
            //currCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));

            newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds,
                BoogieAstFactory.MkGotoCmd(lab3)));
            //new ReturnCmd(Token.NoToken)));

            // lab2
            currLabel = lab2;
            currCmds = new List<Cmd>();

            currCmds.Add(new AssumeCmd(Token.NoToken, aexpr));

            newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds, BoogieAstFactory.MkGotoCmd(lab3)));

            // lab3
            currLabel = lab3;
            currCmds = new List<Cmd>();
        }

        private void recordNotReachableProcLocation(string procName, Block block)
        {
            for (int i = 0; i < block.Cmds.Count; i++)
            {
                var cmd = block.Cmds[i];
                if (cmd is CallCmd && (cmd as CallCmd).Proc != null)
                {
                    if ((cmd as CallCmd).Proc.Name == LanguageSemantics.assertNotReachableName())
                    {
                        allAssertLocations.Add(new AssertLocation(procName, block.Label, i), true);
                    }
                }
            }
        }

        // Return a new local variable
        private string getNewLabel()
        {
            string name = "assert_rewrite_dummy_block_" + (newNameCount.ToString());
            newNameCount++;
            return name;
        }

        // Walk through the trace:
        //   for lab1 & lab2 blocks, replace them with one INTRA instruction
        //   for lab3 blocks, merge with previous
        public ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            var ret = mapBackTraceRec(trace);
            if (failingAssert == null)
            {
                // Walk through the trace to find the failing assert because we didn't
                // find it already
                findAssert(trace);
                if (failingAssert == null && shouldFindAssert)
                {
                    throw new InternalError("Failed to find the failing assert");
                }
            }
            return ret;
        }

        private void findAssert(ErrorTrace trace)
        {
            if (trace == null) return;

            var currLoc = new AssertLocation(trace.procName, "", 0);

            foreach (var blk in trace.Blocks)
            {
                currLoc.blockName = blk.blockName;

                for (int i = 0; i < blk.Cmds.Count; i++)
                {
                    currLoc.instrNo = i;
                    if (allAssertLocations.ContainsKey(currLoc))
                    {
                        if (failingAssert != null)
                        {
                            throw new InternalError("Multiple asserts can fail");
                        }
                        blk.Cmds[i].info = new AssertFailInstrInfo(blk.Cmds[i].info);
                        failingAssert = new AssertLocation(currLoc.procName, currLoc.blockName, currLoc.instrNo);
                    }
                    findAssert(blk.Cmds[i].CalleeTrace);
                }
            }

        }

        private ErrorTrace mapBackTraceRec(ErrorTrace trace)
        {
            var ret = new ErrorTrace(trace.procName);
            ErrorTraceBlock last = null;

            foreach (var blk in trace.Blocks)
            {
                if (lab1BlocksAdded.Contains(blk.blockName))
                {
                    Debug.Assert(last != null);
                    if (blk.Cmds.Count > 1)
                    {
                        var binfo = blk.Cmds[0].info;
                        if (failingAssert != null)
                        {
                            throw new InternalError("Multiple assertions have failed");
                        }
                        failingAssert = new AssertLocation(trace.procName, last.blockName, last.Cmds.Count);

                        if (lab1BlocksAddedForReq.Contains(blk.blockName))
                        {
                            if (last.Cmds.Count == 0)
                                last.info = new RequiresFailInstrInfo(binfo);
                            else
                                last.Cmds.Last().info = new RequiresFailInstrInfo(binfo);
                        }
                        else if (lab1BlocksAddedForEns.Contains(blk.blockName))
                        {
                            if (last.Cmds.Count == 0)
                                last.info = new EnsuresFailInstrInfo(binfo);
                            else
                                last.Cmds.Last().info = new EnsuresFailInstrInfo(binfo);
                        }
                        else
                        {
                            last.addInstr(new IntraInstr(new AssertFailInstrInfo(binfo)));
                        }
                    }
                    else
                    {
                        last.addInstr(new IntraInstr());
                    }

                }
                else if (lab2BlocksAdded.Contains(blk.blockName))
                {
                    Debug.Assert(last != null);
                    InstrInfo info = new InstrInfo();
                    if (blk.Cmds.Count >= 1)
                    {
                        info = new InstrInfo(blk.Cmds[0].info);
                    }
                    if (!lab2BlocksAddedForReqEns.Contains(blk.blockName))
                        last.addInstr(new IntraInstr(info));
                }
                else if (lab3BlocksAdded.Contains(blk.blockName))
                {
                    Debug.Assert(last != null);
                    foreach (var inst in blk.Cmds)
                    {
                        last.addInstr(mapBackInstr(inst));
                    }
                }
                else
                {
                    last = new ErrorTraceBlock(blk.blockName);
                    last.info = blk.info;

                    foreach (var inst in blk.Cmds)
                    {
                        last.addInstr(mapBackInstr(inst));
                    }
                    ret.addBlock(last);
                }
            }
            if (trace.returns) ret.addReturn();

            return ret;
        }

        private ErrorTraceInstr mapBackInstr(ErrorTraceInstr inst)
        {
            if (inst.CalleeTrace == null)
            {
                return inst;
            }

            var cinst = inst as CallInstr;
            Debug.Assert(cinst != null);
            var ret = new CallInstr(mapBackTraceRec(cinst.calleeTrace), cinst.asyncCall, cinst.info);

            return ret;
        }
    }

    public class CallVisitor : FixedVisitor
    {
        Action<CallCmd> action;
        public CallVisitor(Action<CallCmd> action)
        {
            this.action = action;
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            action(node);
            return base.VisitCallCmd(node);
        }
    }

    // Set up a single-threaded program for Stratified Inlining
    public class SequentialInstrumentation : CompilerPass
    {
        // The transformation
        InsertionTrans tinfo;
        // error variable
        GlobalVariable assertsPassed;
        public string assertsPassedName
        {
            get
            {
                if (assertsPassed == null) return null;
                return assertsPassed.Name;
            }
        }

        // Tokenize the assertions


        public SequentialInstrumentation()
        {
            passName = "SequentialInstrumentation";
            tinfo = new InsertionTrans();
            assertsPassed = null;
        }

        private void CreateAssertsPassedVar(Program program)
        {
            var name = "assertsPassed";
            var cnt = 0;
            while (program.TopLevelDeclarations.OfType<GlobalVariable>().Any(g => g.Name == name))
            {
                name = "assertsPassed" + (++cnt);
            }

            assertsPassed = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
                name, Microsoft.Boogie.Type.Bool));
        }

        // If the program has no reachable "async" calls then it is single threaded, i.e., sequential.
        // This call mutates the program by removing all implementations unreachable from main.
        public static bool isSingleThreadProgram(Program program, string mainProcName)
        {
            // Procedures that do an async call
            var asyncCallProcs = new HashSet<string>();

            // Prune unreachable procedures
            var callGraph = new Dictionary<string, HashSet<string>>();

            // call graph
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                callGraph.Add(impl.Name, new HashSet<string>());
                var vs = new CallVisitor(cmd =>
                    {
                        callGraph[impl.Name].Add(cmd.callee);
                        if (hasAsyncAnnotation(cmd))
                        {
                            asyncCallProcs.Add(impl.Name);
                        }
                    });
                vs.VisitImplementation(impl);
            }

            // find reachable procedures
            var reachable = new HashSet<string>();
            reachable.Add(mainProcName);

            // Transitive closure
            var delta = new HashSet<string>(reachable);
            while (delta.Count != 0)
            {
                var nf = new HashSet<string>();
                foreach (var n in delta)
                {
                    if (callGraph.ContainsKey(n)) nf.UnionWith(callGraph[n]);
                }
                delta = nf.Difference(reachable);
                reachable.UnionWith(nf);
            }

            var remainingDecls = new List<Declaration>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                if (decl is Implementation)
                {
                    var name = (decl as Implementation).Name;
                    if (!reachable.Contains(name)) continue;
                }
                remainingDecls.Add(decl);
            }
            program.TopLevelDeclarations = remainingDecls;

            reachable.IntersectWith(asyncCallProcs);
            if (reachable.Count == 0) return true;
            return false;
        }

        static bool hasAsyncAnnotation(Cmd cmd)
        {
            var ccmd = cmd as CallCmd;
            if (ccmd == null) return false;

            return ccmd.IsAsync;
        }

        public static HashSet<string> procsWithAsserts(Program program)
        {
            var pwa = new HashSet<string>();

            // backward call graph
            var callGraph = new Dictionary<string, HashSet<string>>();

            program.TopLevelDeclarations.OfType<Procedure>().Iter(
                proc => callGraph.Add(proc.Name, new HashSet<string>()));

            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    foreach (var cmd in blk.Cmds.OfType<CallCmd>())
                    {
                        callGraph[cmd.callee].Add(impl.Name);
                    }

                    foreach (var cmd in blk.Cmds.OfType<AssertCmd>())
                    {
                        if (!BoogieUtil.isAssertTrue(cmd))
                        {
                            pwa.Add(impl.Name);
                            break;
                        }
                    }
                }
            }

            // find reachable procedures
            var reachable = new HashSet<string>();
            reachable.UnionWith(pwa);
            reachable.Add(LanguageSemantics.assertNotReachableName());

            // Transitive closure
            var delta = new HashSet<string>(reachable);
            while (delta.Count != 0)
            {
                var nf = new HashSet<string>();
                foreach (var n in delta)
                {
                    if (callGraph.ContainsKey(n)) nf.UnionWith(callGraph[n]);
                }
                delta = nf.Difference(reachable);
                reachable.UnionWith(nf);
            }

            return reachable;
        }

        public override CBAProgram runCBAPass(CBAProgram program)
        {
            CreateAssertsPassedVar(program);
            var impls = BoogieUtil.nameImplMapping(program);
            var pwa = procsWithAsserts(program);

            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                var instrumented = new List<Block>();
                foreach (var blk in impl.Blocks)
                {
                    var currCmds = new List<Cmd>();
                    var currLabel = blk.Label;

                    tinfo.addTrans(impl.Name, blk.Label, blk.Label);
                    var incnt = -1;
                    foreach (Cmd cmd in blk.Cmds)
                    {
                        incnt++;

                        // replace "t := getThreadID" with "t := 1"
                        if (BoogieUtil.checkIsCall(LanguageSemantics.getThreadIDName(), cmd))
                        {
                            var ccmd = cmd as CallCmd;
                            var outv = ccmd.Outs[0];
                            if (outv == null)
                            {
                                currCmds.Add(cmd);
                                addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);
                                continue;
                            }
                            currCmds.Add(BoogieAstFactory.MkVarEqConst(outv.Decl, 1));
                            addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);
                            continue;
                        }

                        // Remove yield statements
                        if (cmd is YieldCmd)
                        {
                            currCmds.Add(BoogieAstFactory.MkAssume(Expr.True));
                            addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);
                            continue;
                        }

                        // instrument assert
                        if (cmd is AssertCmd && !BoogieUtil.isAssertTrue(cmd))
                        {
                            currCmds.Add(BoogieAstFactory.MkVarEqExpr(assertsPassed, (cmd as AssertCmd).Expr));
                            addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);

                            currLabel = addInstr(instrumented, currCmds, currLabel);
                            currCmds = new List<Cmd>();

                            continue;
                        }

                        // is assert false
                        if (BoogieUtil.checkIsCall(LanguageSemantics.assertNotReachableName(), cmd))
                        {
                            currCmds.Add(BoogieAstFactory.MkVarEqExpr(assertsPassed, Expr.False));
                            addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);

                            currLabel = addInstr(instrumented, currCmds, currLabel);
                            currCmds = new List<Cmd>();

                            continue;
                        }

                        // procedure call 
                        if (cmd is CallCmd && pwa.Contains((cmd as CallCmd).callee))
                        {
                            currCmds.Add(cmd);
                            addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);
                            currLabel = addInstr(instrumented, currCmds, currLabel);
                            currCmds = new List<Cmd>();
                            continue;
                        }

                        currCmds.Add(cmd);
                        addedTrans(impl.Name, blk.Label, incnt, cmd, currLabel, currCmds);

                    }

                    instrumented.Add(new Block(Token.NoToken, currLabel, currCmds, blk.TransferCmd));

                }

                impl.Blocks = instrumented;
            }

            program.AddTopLevelDeclaration(assertsPassed);
            addMain(program);

            BoogieUtil.DoModSetAnalysis(program);

            // Set inline attribute
            // free requires assertsPassed == true;
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                impl.Proc.Requires.Add(new Requires(true, Expr.Ident(assertsPassed)));
            }

            // convert free ensures e to:
            //  free ensures assertsPassed == false || e
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => pwa.Contains(impl.Name)))
            {
                foreach (Ensures ens in impl.Proc.Ensures)
                    ens.Condition = Expr.Or(Expr.Not(Expr.Ident(assertsPassed)), ens.Condition);
            }

            return program;
        }

        // Adds a new main:
        //   assertsPassed := true;
        //   call main();
        //   assert assertsPassed;
        void addMain(CBAProgram program)
        {
            var dup = new FixedDuplicator();
            var origMain = BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, program.mainProcName);
            var newMain = dup.VisitImplementation(origMain);
            var newProc = dup.VisitProcedure(origMain.Proc);

            newMain.Name += "_SeqInstr";
            newProc.Name += "_SeqInstr";
            newMain.Proc = newProc;

            var mainIns = new List<Expr>();
            foreach (Variable v in newMain.InParams)
            {
                mainIns.Add(Expr.Ident(v));
            }
            var mainOuts = new List<IdentifierExpr>();
            foreach (Variable v in newMain.OutParams)
            {
                mainOuts.Add(Expr.Ident(v));
            }

            var callMain = new CallCmd(Token.NoToken, program.mainProcName, mainIns, mainOuts);
            callMain.Proc = origMain.Proc;

            var cmds = new List<Cmd>();
            cmds.Add(BoogieAstFactory.MkVarEqConst(assertsPassed, true));
            cmds.Add(callMain);
            cmds.Add(new AssertCmd(Token.NoToken, Expr.Ident(assertsPassed)));

            var blk = new Block(Token.NoToken, "start", cmds, new ReturnCmd(Token.NoToken));
            newMain.Blocks = new List<Block>();
            newMain.LocVars = new List<Variable>();
            newMain.Blocks.Add(blk);

            program.AddTopLevelDeclaration(newProc);
            program.AddTopLevelDeclaration(newMain);

            program.mainProcName = newMain.Name;

            // Set entrypoint
            origMain.Attributes = BoogieUtil.removeAttr("entrypoint", origMain.Attributes);
            origMain.Proc.Attributes = BoogieUtil.removeAttr("entrypoint", origMain.Proc.Attributes);

            newMain.AddAttribute("entrypoint");
        }


        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            // knock off top-level procedure
            var OldMainName = (input as PersistentCBAProgram).mainProcName;
            ErrorTrace ptrace = null;
            foreach (var blk in trace.Blocks)
            {
                var c = blk.Cmds.OfType<CallInstr>().First(cmd => cmd.callee == OldMainName);
                if (c == null) continue;
                ptrace = c.calleeTrace;
                break;
            }

            return tinfo.mapBackTrace(ptrace);
        }

        // goto label1, label2;
        //
        // label1:
        //   assume !assertsPassed;
        //   return;
        //
        // label2:
        //   assume assertsPassed;
        //   goto lab;
        //
        // lab:
        //
        // Inputs: the list of blocks being constructed; the current block being constructed.
        // End current block and adds two new blocks.
        // Returns "lab".

        private string addInstr(List<Block> instrumented, List<Cmd> curr, string curr_label)
        {
            string lbl1 = getNewLabel();
            string lbl2 = getNewLabel();

            List<String> ssp = new List<String> { lbl1, lbl2 };
            instrumented.Add(new Block(Token.NoToken, curr_label, curr, new GotoCmd(Token.NoToken, ssp)));

            string common_label = getNewLabel();
            // assume (!assertsPassed)
            AssumeCmd cmd1 = new AssumeCmd(Token.NoToken, Expr.Not(Expr.Ident(assertsPassed)));
            // assume (assertsPassed)
            AssumeCmd cmd2 = new AssumeCmd(Token.NoToken, Expr.Ident(assertsPassed));

            curr = new List<Cmd>();
            curr.Add(cmd1);
            instrumented.Add(new Block(Token.NoToken, lbl1, curr, new ReturnCmd(Token.NoToken)));

            curr = new List<Cmd>();
            curr.Add(cmd2);
            instrumented.Add(new Block(Token.NoToken, lbl2, curr, BoogieAstFactory.MkGotoCmd(common_label)));

            return common_label;
        }

        static int labelCnt = 0;

        static string getNewLabel()
        {
            labelCnt++;
            return "SeqInstr_" + labelCnt.ToString();
        }

        // Record the fact that we added instruction corresponding to "in" as the last instruction
        // of "curr"
        private void addedTrans(string procName, string inBlk, int inCnt, Cmd inCmd, string outBlk, List<Cmd> curr)
        {
            List<Cmd> cseq = new List<Cmd>();
            cseq.Add(curr.Last());
            tinfo.addTrans(procName, inBlk, inCnt, inCmd, outBlk, curr.Count - 1, cseq);
        }
    }
}

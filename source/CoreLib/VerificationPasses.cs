using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;


namespace cba
{
    /* A verification pass is one that actually calls Boogie to get an error trace */
    public class VerificationPass : CompilerPass
    {
        // Did the call to Boogie succeed (i.e., returned "verified")?
        public bool success { get; protected set; }

        // Did the verification reach the recursion bound?
        public bool reachedBound { get; private set; }

        // The error traces
        public List<ErrorTrace> traces { get; protected set; }

        // The first trace
        public ErrorTrace trace
        {
            get
            {
                if (traces == null || traces.Count == 0)
                    return null;
                return traces[0];
            }
        }

        // Error trace needed?
        protected bool needErrorTraces;

        // The set of global variables that were used in proof of correctness
        // TODO: This is not yet computed!
        //public Set<string> globalsUsedForProof { get; private set; }

        // For pruning a program
        PruneProgramPass prune;
        public static bool usePruning = true;

        // The set of global variables whose value should be recorded in the trace.
        // Precondition: All of these are "int" variables.
        protected HashSet<string> varsToRecord;
        bool recordTransformationHappened;

        // Name of procedure that records its argument's concrete value
        public static string recordArgProcPrefix = "boogie_si_record";
        string recordIntArgProc;
        string recordBoolArgProc;

        // Is Boogie going to give us a model
        static bool WillGetModel
        {
            get
            {
                return BoogieVerify.options.UseProverEvaluate || !BoogieVerify.options.StratifiedInliningWithoutModels;
            }
        }

        // For debugging
        public static TimeSpan tempTime = TimeSpan.Zero;
        public static bool measureTempTime = false;

        public VerificationPass(bool cex)
            : base()
        {
            passName = "Some verification pass";
            success = false;
            reachedBound = false;
            traces = new List<ErrorTrace>();
            prune = null;
            needErrorTraces = cex;
            //globalsUsedForProof = new Set<string>();
            varsToRecord = new HashSet<string>();
            recordTransformationHappened = false;
            recordIntArgProc = recordArgProcPrefix + "_vp_special_int";
            recordBoolArgProc = recordArgProcPrefix + "_vp_special_bool";
        }

        public VerificationPass(bool cex, params string[] varsToRecord)
            : this(cex)
        {
            this.varsToRecord = new HashSet<string>();
            varsToRecord.Iter(s => this.varsToRecord.Add(s));
            if (varsToRecord.Length != 0 && !WillGetModel)
                Debug.Assert(false, "Model generation is turned off -- cannot record values");

        }

        public VerificationPass(bool cex, HashSet<string> varsToRecord)
            : this(cex)
        {
            this.varsToRecord = varsToRecord;
        }

        public override CBAProgram runCBAPass(CBAProgram prog)
        {
            if (usePruning)
            {
                return runVerificationPass(input as PersistentCBAProgram);
            }
            return feedToBoogie(prog);
        }

        // Returns a program that only contains the counterexample
        public CBAProgram runVerificationPass(PersistentCBAProgram prog)
        {
            prune = new PruneProgramPass();
            var pruned = prune.run(prog) as PersistentCBAProgram;
            CBAProgram p = pruned.getCBAProgram();

            return feedToBoogie(p);
        }

        private CBAProgram feedToBoogie(CBAProgram p) {
            // Do typechecking 
            if (BoogieUtil.TypecheckProgram(p as Program, "verificationPass"))
            {
                BoogieUtil.PrintProgram(p, "error.bpl");
                throw new InvalidProg("Cannot typecheck");
            }

            BoogieVerify.options.Set();

            // An important pass for recording the value of int variables
            Debug.Assert(CommandLineOptions.Clo.StratifiedInlining > 0);
            if(WillGetModel)
              recordVarsTransformation(p, p.mainProcName);

            //System.Diagnostics.Debugger.Break();
            
            var counterexamples = new List<BoogieErrorTrace>();
            BoogieVerify.ReturnStatus ret;
            if (needErrorTraces)
            {
                ret = BoogieVerify.Verify(p as Program, out counterexamples, true /* isCBA */);
            }
            else
            {
                ret = BoogieVerify.Verify(p as Program);
            }

            success = (ret != BoogieVerify.ReturnStatus.NOK);
            reachedBound = (ret == BoogieVerify.ReturnStatus.ReachedBound);

            if (!needErrorTraces)
            {
                return null;
            }

            if (varsToRecord.Count != 0 && !WillGetModel)
                Debug.Assert(false, "Model generation is turned off -- cannot record values");

            // Currently, we're only concerned with one counterexample.
            foreach (var et in counterexamples)
            {
                Debug.Assert(et is BoogieAssertErrorTrace);

                var cnt = 1;
                var etrace = constructErrorTrace(et.cex, et.impl.Name, false, ref cnt);

                if(prune != null)  etrace = prune.mapBackTrace(etrace);
                traces.Add(etrace);

                //PrintProgramPath.print(input, etrace, "tt");
            }

            return null;
        }

        // Records the value of k after every context switch
        void recordVarsTransformation(Program program, string mainProcName)
        {
            if (varsToRecord.Count == 0) return;

            recordTransformationHappened = true;
            
            // Add declaration for the recording procedure, if not already present
            Procedure intDecl = BoogieUtil.findProcedureDecl(program.TopLevelDeclarations, recordIntArgProc);
            if (intDecl == null)
            {
                var inv = new List<Variable>();
                inv.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Int), true));

                intDecl = new Procedure(Token.NoToken, recordIntArgProc, new List<TypeVariable>(), inv, new List<Variable>(), new List<Requires>(),
                    new List<IdentifierExpr>(), new List<Ensures>());

                program.AddTopLevelDeclaration(intDecl);
            }

            Procedure boolDecl = BoogieUtil.findProcedureDecl(program.TopLevelDeclarations, recordBoolArgProc);
            if (boolDecl == null)
            {
                var inv = new List<Variable>();
                inv.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Bool), true));

                boolDecl = new Procedure(Token.NoToken, recordBoolArgProc, new List<TypeVariable>(), inv, new List<Variable>(), new List<Requires>(),
                    new List<IdentifierExpr>(), new List<Ensures>());

                program.AddTopLevelDeclaration(boolDecl);
            }

            // Get the set of implementations in the program
            var impls = new HashSet<string>();
            BoogieUtil.GetImplementations(program).Iter(impl => impls.Add(impl.Name));

            // Gather the set of constants whose values have to be recorded
            var constantsToRecord = new HashSet<Constant>();
            program.TopLevelDeclarations.OfType<Constant>()
                .Where(g => varsToRecord.Contains(g.Name))
                .Iter(g => constantsToRecord.Add(g as Constant));

            // Add the record call after every Cmd that modifies a variable
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                // record constants at the beginning of main
                if (impl.Name == mainProcName && constantsToRecord.Any())
                {
                    var ncmds = new List<Cmd>();
                    foreach (var v in constantsToRecord)
                    {
                        CallCmd rc = null;
                        if (v.TypedIdent.Type.IsInt)
                        {
                            rc = new CallCmd(Token.NoToken, recordIntArgProc, new List<Expr>{Expr.Ident(v)}, new List<IdentifierExpr>());
                            rc.Proc = intDecl;
                        }
                        else
                        {
                            rc = new CallCmd(Token.NoToken, recordBoolArgProc, new List<Expr>{Expr.Ident(v)}, new List<IdentifierExpr>());
                            rc.Proc = boolDecl;
                        }
                        ncmds.Add(rc);
                    }
                    ncmds.AddRange(impl.Blocks[0].Cmds);
                    impl.Blocks[0].Cmds = ncmds;
                }

                foreach (var block in impl.Blocks)
                {
                    var newCmds = new List<Cmd>();
                    bool changed = false;
                    foreach (Cmd cmd in block.Cmds)
                    {
                        newCmds.Add(cmd);
                        var modVars = BoogieUtil.getVarsModified(cmd, impls);
                        modVars.IntersectWith(varsToRecord);
                        if (modVars.Count == 0)
                            continue;

                        changed = true;
                        foreach (var m in modVars)
                        {
                            var rc = getRecordCmd(m, cmd, intDecl, boolDecl);
                            if (rc == null) continue;
                            newCmds.Add(rc);
                        }

                    }
                    if (changed)
                    {
                        block.Cmds = newCmds;
                    }
                }
            }

        }

        private CallCmd getRecordCmd(string varName, Cmd cmd, Procedure intDecl, Procedure boolDecl)
        {
            var fv = new FindVars();
            fv.Visit(cmd);
            Debug.Assert(fv.varsFound.ContainsKey(varName));

            var v = fv.varsFound[varName];

            Debug.Assert(v != null);
            if (!v.TypedIdent.Type.IsInt && !v.TypedIdent.Type.IsBool) return null;

            var ins = new List<Expr>();
            ins.Add(Expr.Ident(v));

            CallCmd rc = null;
            if (v.TypedIdent.Type.IsInt)
            {
                rc = new CallCmd(Token.NoToken, recordIntArgProc, ins, new List<IdentifierExpr>());
                rc.Proc = intDecl;
            }
            else
            {
                rc = new CallCmd(Token.NoToken, recordBoolArgProc, ins, new List<IdentifierExpr>());
                rc.Proc = boolDecl;
            }

            return rc;
        }

        // Construct a ErrorTrace from a Counterexample of procedure procName
        // (possibly interprocedural). The flag "completeTrace" says if btrace
        // is expected to be a trace from entry to exit of the procedure or not
        //
        // captureStateIndex: current index into btrace.model.States
        protected ErrorTrace constructErrorTrace(Counterexample btrace, string procName,
            bool completeTrace, ref int captureStateIndex)
        {
            if(btrace == null) return null;

            var ret = new ErrorTrace(procName);

            // All blocks, except the last are complete blocks
            for (int i = 0, n = btrace.Trace.Count - 1; i < n; i++)
            {
                var blk = btrace.Trace[i];
                var etblk = new ErrorTraceBlock(blk.Label);
                etblk.info = new InstrInfo();

                ErrorTraceInstr lastInstr = null;

                for (int numInstr = 0; numInstr < blk.Cmds.Count; numInstr++) 
                {
                    Cmd c = blk.Cmds[numInstr];
                    var loc = new TraceLocation(i, numInstr);
                    ErrorTraceInstr instr = null;

                    if (btrace.calleeCounterexamples.ContainsKey(loc))
                    {
                        ErrorTrace calleeTrace = constructErrorTrace(
                             btrace.calleeCounterexamples[loc].counterexample, (c as CallCmd).Proc.Name, true, ref captureStateIndex);
                        var info = new InstrInfo();
                        var cc = c as CallCmd;
                        Debug.Assert(cc != null);

                        if (cc.Proc.Name == recordIntArgProc || cc.Proc.Name == recordBoolArgProc )
                        {
                            Debug.Assert(recordTransformationHappened);
                            Debug.Assert(btrace.calleeCounterexamples[loc].args.Count == 1);
                            Debug.Assert(cc.Ins[0] is IdentifierExpr);

                            var modelVal = btrace.calleeCounterexamples[loc].args[0];
                            object v = null;
                            if (cc.Proc.Name == recordIntArgProc && modelVal is Model.Integer)
                            {
                                // TODO: need a better fix for BigNums
                                //v = (modelVal as Model.Integer).AsInt();
                                v = Microsoft.BaseTypes.BigNum.FromString((modelVal as Model.Integer).Numeral);
                            }
                            else if (cc.Proc.Name == recordIntArgProc && modelVal is int)
                            {
                                v = (int)modelVal;
                            }
                            else if (cc.Proc.Name == recordIntArgProc && modelVal is Microsoft.BaseTypes.BigNum)
                            {
                                v = BoogieUtil.BigNumToIntForce((Microsoft.BaseTypes.BigNum)modelVal);
                            }
                            else if(modelVal is Model.Boolean)
                            {
                                v = (modelVal as Model.Boolean).Value;
                            }
                            else if (modelVal is bool)
                            {
                                v = (bool)modelVal;
                            }
                            else
                            {
                                Debug.Assert(false);
                            }
                            if (lastInstr != null && lastInstr.info != null)
                                lastInstr.info.addVal((cc.Ins[0] as IdentifierExpr).Name, v);
                            else
                                etblk.info.addVal((cc.Ins[0] as IdentifierExpr).Name, v);
                            continue;
                        }
                        if (cc.Proc.Name.StartsWith(recordArgProcPrefix))
                        {
                            Debug.Assert(btrace.calleeCounterexamples[loc].args.Count == 1);
                            //Debug.Assert(cc.Ins[0] is IdentifierExpr);

                            var v = btrace.calleeCounterexamples[loc].args[0];
                            if (v != null)
                            {
                                info.addVal("si_arg", v);
                            }
                        }
                        instr = new CallInstr(cc.Proc.Name, calleeTrace, false, info);
                    }
                    else if (c is CallCmd)
                    {
                        var callee = (c as CallCmd).Proc.Name;
                        instr = new CallInstr(callee);
                    }
                    else
                    {
                        var ac = c as AssumeCmd;
                        if (ac != null && btrace.Model != null && QKeyValue.FindStringAttribute(ac.Attributes, "captureState") == "corral_capture")
                        {
                            var info = new ModelInstrInfo(btrace.Model, captureStateIndex);
                            instr = new IntraInstr(info);
                            captureStateIndex++;
                        }
                        else
                        {
                            instr = new IntraInstr();
                        }
                    }
                    lastInstr = instr;
                    etblk.addInstr(instr);
                }
                ret.addBlock(etblk);
            }

            // The last block has the failing assertion -- we assume this assertion
            // to be the last one of the block
            var lastBlk = btrace.Trace[btrace.Trace.Count - 1];
            var lastBlkLen = lastBlk.Cmds.Count - 1;
            
            if (!completeTrace)
            {
                lastBlkLen = -1;
                for (int i = lastBlk.Cmds.Count - 1; i >= 0; i--)
                {
                    if (lastBlk.Cmds[i] is AssertCmd)
                    {
                        lastBlkLen = i;
                        break;
                    }
                }
                if (lastBlkLen == -1)
                {
                    throw new InternalError("Failed to find the failing assert");
                }
            }

            ErrorTraceInstr lastInstr2 = null;

            var lastEtBlk = new ErrorTraceBlock(lastBlk.Label);
            lastEtBlk.info = new InstrInfo();
            for (int i = 0; i <= lastBlkLen; i++)
            {
                var c = lastBlk.Cmds[i];
                var loc = new TraceLocation(btrace.Trace.Count - 1, i);
                ErrorTraceInstr instr = null;
                if (btrace.calleeCounterexamples.ContainsKey(loc))
                {
                    var calleeTrace = constructErrorTrace(
                        btrace.calleeCounterexamples[loc].counterexample, (c as CallCmd).Proc.Name, true, ref captureStateIndex);
                    var info = new InstrInfo();

                    var cc = c as CallCmd;
                    Debug.Assert(cc != null);

                    if (cc.Proc.Name == recordIntArgProc || cc.Proc.Name == recordBoolArgProc)
                    {
                        Debug.Assert(recordTransformationHappened);
                        Debug.Assert(btrace.calleeCounterexamples[loc].args.Count == 1);
                        Debug.Assert(cc.Ins[0] is IdentifierExpr);

                        var modelVal = btrace.calleeCounterexamples[loc].args[0];
                        object v = null;
                        if (cc.Proc.Name == recordIntArgProc && modelVal is Model.Integer)
                        {
                            // TODO: need a better fix for BigNums
                            //v = (modelVal as Model.Integer).AsInt();
                            v = Microsoft.BaseTypes.BigNum.FromString((modelVal as Model.Integer).Numeral);
                        }
                        else if (cc.Proc.Name == recordIntArgProc && modelVal is int)
                        {
                            v = (int)modelVal;
                        }
                        else if (cc.Proc.Name == recordIntArgProc && modelVal is Microsoft.BaseTypes.BigNum)
                        {
                            v = BoogieUtil.BigNumToIntForce((Microsoft.BaseTypes.BigNum)modelVal);
                        }
                        else if (modelVal is Model.Boolean)
                        {
                            v = (modelVal as Model.Boolean).Value;
                        }
                        else if (modelVal is bool)
                        {
                            v = (bool)modelVal;
                        }
                        else
                        {
                            Debug.Assert(false);
                        }
                        if (lastInstr2 != null && lastInstr2.info != null)
                            lastInstr2.info.addVal((cc.Ins[0] as IdentifierExpr).Name, v);
                        else
                            lastEtBlk.info.addVal((cc.Ins[0] as IdentifierExpr).Name, v);
                        continue;
                    }
                    else if (cc.Proc.Name.StartsWith(recordArgProcPrefix))
                    {
                        Debug.Assert(btrace.calleeCounterexamples[loc].args.Count == 1);
                        //Debug.Assert(cc.Ins[0] is IdentifierExpr);

                        var v = btrace.calleeCounterexamples[loc].args[0];
                        if (v != null)
                        {
                            info.addVal("si_arg", v);
                        }
                    }

                    instr = new CallInstr(cc.Proc.Name, calleeTrace, false, info);
                }
                else if (c is CallCmd)
                {
                    var callee = (c as CallCmd).Proc.Name;
                    instr = new CallInstr(callee);
                }
                else
                {
                    var ac = c as AssumeCmd;
                    if (ac != null && btrace.Model != null && QKeyValue.FindStringAttribute(ac.Attributes, "captureState") == "corral_capture")
                    {
                        var info = new ModelInstrInfo(btrace.Model, captureStateIndex);
                        instr = new IntraInstr(info);
                        captureStateIndex++;
                    }
                    else
                    {
                        instr = new IntraInstr();
                    }
                }
                lastInstr2 = instr;
                lastEtBlk.addInstr(instr);
            }

            ret.addBlock(lastEtBlk);

            if (completeTrace)
            {
                ret.addReturn();
            }

            return ret;
        }

    }





    // Runs the Boogie verifier. Assumes that the program has not been inlined.
    public class StaticInlineAndVerifyPass : VerificationPass
    {
        StaticInliningAndUnrollingPass inliningPass;

        public StaticInlineAndVerifyPass(StaticSettings settings, bool needErrorTrace)
            : base(needErrorTrace)
        {
            passName = "Inline and verify pass";
            inliningPass = new StaticInliningAndUnrollingPass(settings);
        }

        public StaticInlineAndVerifyPass(StaticSettings settings, bool needErrorTrace, HashSet<string> varsToRecord)
            : base(needErrorTrace, varsToRecord)
        {
            passName = "Inline and verify pass";
            inliningPass = new StaticInliningAndUnrollingPass(settings);
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            // Do Inlining
            var prog = inliningPass.run(input);
            
            runVerificationPass(prog as PersistentCBAProgram);

            if (needErrorTraces)
            {
                // Map back trace
                for (int i = 0; i < traces.Count; i++)
                {
                    traces[i] = inliningPass.mapBackTrace(traces[i]);
                }
            }

            return null;
        }
    }

    // Common things for pruning a program, making it easier
    // for Verification
    public class PruneProgramPass : CompilerPass
    {
        // Unused Variable elimination
        UnReadVarEliminator varEliminator;

        // For compressing basic blocks
        CompressBlocks compressBlocks;

        // Remove unreachable procedures in the call graph?
        public static bool RemoveUnreachable = false;

        // Normalize statements
        public static bool normalizeStatements = false;

        public PruneProgramPass()
            : this(true)
        {

        }

        public PruneProgramPass(bool compress)
            : base()
        {
            passName = "Pruning program";
            varEliminator = null;
            if (!compress) compressBlocks = null;
            else compressBlocks = new CompressBlocks();
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            // Remove unreachable procedures
            if (RemoveUnreachable) BoogieUtil.pruneProcs(p, p.mainProcName);

            // normalize commands
            if (normalizeStatements) p.TopLevelDeclarations.OfType<Implementation>().Iter(normalizeImpl);
 
            // Re-do modset analysis
            BoogieUtil.DoModSetAnalysis(p);
            
            // Eliminate local variables that are never used (i.e., their value is never read)
            varEliminator = new UnReadVarEliminator();
            varEliminator.run(p);

            // Eliminate dead variables -- does not change the program.
            UnusedVarEliminator.Eliminate(p); 
            
            // Remove annotations that won't parse because of dropped variables
            RemoveVarsFromAttributes.Prune(p);

            // Compress basic blocks
            if(compressBlocks!=null)
              compressBlocks.VisitProgram(p);
            
            return p;
        }


        // Change:
        //   Mem := Mem[x := v]
        // to:
        //   Mem[x] := v
        // and:
        //   x := x;
        // to:
        //   assume true;  
        private void normalizeImpl(Implementation impl)
        {
            foreach (var blk in impl.Blocks)
            {
                for (int i = 0; i < blk.Cmds.Count; i++)
                {
                    var cmd = blk.Cmds[i] as AssignCmd;
                    if (cmd == null) continue;
                    if (cmd.Lhss.Count != 1) continue;

                    var lhs = cmd.Lhss[0] as SimpleAssignLhs;
                    if (lhs == null) continue;
                    if (!lhs.AssignedVariable.Decl.TypedIdent.Type.IsMap) continue;

                    var rhs = cmd.Rhss[0] as NAryExpr;
                    if (rhs == null) continue;
                    if (rhs.Fun.FunctionName != "MapStore") continue;
                    if (rhs.Args.Count != 3) continue;
                    var arg1 = rhs.Args[0] as IdentifierExpr;
                    if (arg1 == null) continue;

                    // The map variable is the same on both side
                    if (lhs.AssignedVariable.Decl.Name != arg1.Decl.Name) continue;

                    blk.Cmds[i] = BoogieAstFactory.MkMapAssign(arg1.Decl, rhs.Args[1], rhs.Args[2]);
                }

                for (int i = 0; i < blk.Cmds.Count; i++)
                {
                    var cmd = blk.Cmds[i] as AssignCmd;
                    if (cmd == null) continue;
                    if (cmd.Lhss.Count != 1) continue;

                    var lhs = cmd.Lhss[0] as SimpleAssignLhs;
                    if (lhs == null) continue;

                    var rhs = cmd.Rhss[0] as IdentifierExpr;
                    if (rhs == null) continue;

                    if (lhs.AssignedVariable.Name != rhs.Decl.Name)
                        continue;

                    blk.Cmds[i] = BoogieAstFactory.MkAssume(Expr.True);
                }
            }
        }


        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            if(compressBlocks != null)
                trace = compressBlocks.mapBackTrace(trace);
            return varEliminator.mapBackTrace(trace);
            
            //return trace;
        }
    }

    // Common things for pruning a program, making it easier
    // for Verification
    public class PruneLocals : CompilerPass
    {
        // Unused Variable elimination
        UnReadVarEliminator varEliminator;

        public PruneLocals()
            : base()
        {
            passName = "Pruning program";
            varEliminator = null;
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {

            // Re-do modset analysis
            BoogieUtil.DoModSetAnalysis(p);

            // Eliminate local variables that are never used (i.e., their value is never read)
            varEliminator = new UnReadVarEliminator(true);
            varEliminator.run(p);

            // Eliminate dead variables -- does not change the program.
            UnusedVarEliminator.Eliminate(p);

            return p;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return varEliminator.mapBackTrace(trace);

            //return trace;
        }
    }

    public class DeepAssertRewrite : CompilerPass
    {
        string origMain;

        Dictionary<string, string> firstBlockToImpl;
        
        // newBlock -> <origBlock, Proc>
        Dictionary<string, Tuple<string, string>> blockToOrig;
        
        // continue blocks
        HashSet<string> assertContinueBlocks;
        HashSet<string> callContinueBlocks;

        // exit blocks
        HashSet<string> exitBlocks; // for assert
        HashSet<string> callInlinedBlocks; // for calls

        // number of procs inlined into main
        public int procsIncludedInMain { get; private set; }

        // disable loop transformation
        public static bool disableLoops = false;

        public DeepAssertRewrite()
        {
            origMain = null;
            firstBlockToImpl = new Dictionary<string, string>();
            blockToOrig = new Dictionary<string, Tuple<string, string>>();
            assertContinueBlocks = new HashSet<string>();
            callContinueBlocks = new HashSet<string>();
            exitBlocks = new HashSet<string>();
            callInlinedBlocks = new HashSet<string>();
            procsIncludedInMain = 0;
        }

        public override CBAProgram runCBAPass(CBAProgram program)
        {
            // Prepare for stratified inlining with assertions
            var procsThatCannotReachAssert = new HashSet<string>();
            program.TopLevelDeclarations.OfType<Procedure>().Iter(proc => procsThatCannotReachAssert.Add(proc.Name));
            procsThatCannotReachAssert.ExceptWith(SequentialInstrumentation.procsWithAsserts(program));

            if (procsThatCannotReachAssert.Contains(program.mainProcName))
                return program;

            if (!disableLoops)
            {
                // loopy guys cannot reach asserts
                program.TopLevelDeclarations.OfType<LoopProcedure>()
                    .Iter(proc => procsThatCannotReachAssert.Add(proc.Name));

                program.TopLevelDeclarations.OfType<Procedure>()
                    .Where(proc => QKeyValue.FindBoolAttribute(proc.Attributes, "LoopProcedure"))
                    .Iter(proc => procsThatCannotReachAssert.Add(proc.Name));
            }

            // Make copies of all procedures that can reach assert
            var implCopy = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => !procsThatCannotReachAssert.Contains(impl.Name))
                .Iter(impl => implCopy.Add(impl.Name,
                    (new FixedDuplicator(true)).VisitImplementation(impl)));

            procsIncludedInMain = implCopy.Count;

            // Disable assertions in the original procedures
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl =>
                    impl.Blocks.Iter(blk =>
                    {
                        for (int i = 0; i < blk.Cmds.Count; i++)
                        {
                            var ac = blk.Cmds[i] as AssertCmd;
                            if (ac != null) blk.Cmds[i] = new AssumeCmd(ac.tok, ac.Expr);
                        }
                    }));

            // Identify main
            var main = program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"))
                .FirstOrDefault();
            if (main == null)
                main = BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, program.mainProcName);

            var mainName = main.Name;
            origMain = main.Name;

            // delete entrypoint attribute
            main.Attributes = BoogieUtil.removeAttr("entrypoint", main.Attributes);
            main.Proc.Attributes = BoogieUtil.removeAttr("entrypoint", main.Proc.Attributes);

            // rename stuff
            implCopy.Values
                .Where(impl => impl.Name != mainName)
                .Iter(impl => RenameImpl(impl));

            // Add all procedures to main
            var implToFirstBlock = new Dictionary<string, Block>();
            implCopy.Values
                .Iter(impl => implToFirstBlock.Add(impl.Name, impl.Blocks[0]));

            var mainCopy = implCopy[mainName];
            mainCopy.Blocks.Iter(blk => blockToOrig.Add(blk.Label, Tuple.Create(blk.Label, origMain)));

            mainCopy.AddAttribute("entrypoint");

            // Merge impls
            foreach (var impl in implCopy.Values)
            {
                if (impl.Name == mainName)
                    continue;
                // union locals
                mainCopy.LocVars.AddRange(impl.LocVars);
                // formals have already been substituted by locals
                mainCopy.LocVars.AddRange(impl.OutParams);
                mainCopy.LocVars.AddRange(impl.InParams);

                mainCopy.Blocks.AddRange(impl.Blocks);
            }

            // Block return in main
            foreach (var blk in mainCopy.Blocks.Where(b => b.TransferCmd is ReturnCmd))
                blk.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));

            // Change name of new main
            mainCopy.Name = "new" + mainCopy.Name;

            // Edit procedure calls in the copied impls
            var newLabCnt = 0;
            var GetNewLabel = new Func<string>(() =>
            {
                return "sia_lab" + (newLabCnt++);
            });

            var GetExitBlock = new Func<Block>(() =>
                new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(), new ReturnCmd(Token.NoToken)));

            var newBlocks1 = new List<Block>();
            var newBlocks2 = new List<Block>();

            foreach (var blk in mainCopy.Blocks)
            {
                var currBlock = new Block(blk.tok, blk.Label, new List<Cmd>(), null);

                foreach (var cmd in blk.Cmds)
                {
                    var acmd = cmd as AssertCmd;
                    if (acmd != null && !(acmd.Expr is LiteralExpr && (acmd.Expr as LiteralExpr).IsTrue))
                    {
                        // split for assertion
                        var lab = GetNewLabel();
                        var nblk = new Block(Token.NoToken, lab, new List<Cmd>(), null);
                        var eb = GetExitBlock();

                        // Finish current block
                        currBlock.TransferCmd = new GotoCmd(Token.NoToken, new List<Block> { nblk, eb });
                        eb.Cmds.Add(new AssertCmd(acmd.tok, acmd.Expr, acmd.Attributes));
                        nblk.Cmds.Add(new AssumeCmd(acmd.tok, acmd.Expr));

                        newBlocks2.Add(eb);
                        newBlocks1.Add(currBlock);
                        currBlock = nblk;

                        assertContinueBlocks.Add(nblk.Label);
                        exitBlocks.Add(eb.Label);

                        continue;
                    }

                    var ccmd = cmd as CallCmd;
                    if (ccmd != null && implToFirstBlock.ContainsKey(ccmd.callee))
                    {
                        var lab = GetNewLabel();
                        var afBlk = new Block(Token.NoToken, lab, new List<Cmd>(), BoogieAstFactory.MkGotoCmd(implToFirstBlock[ccmd.callee].Label));
                        callInlinedBlocks.Add(afBlk.Label);

                        // formal-in := actuals
                        for (int i = 0; i < implCopy[ccmd.callee].InParams.Count; i++)
                        {
                            var formal = implCopy[ccmd.callee].InParams[i];
                            var actual = ccmd.Ins[i];
                            afBlk.Cmds.Add(BoogieAstFactory.MkVarEqExpr(formal, actual));
                        }

                        lab = GetNewLabel();
                        var nblk = new Block(Token.NoToken, lab, new List<Cmd>(), null);

                        // Finish current block
                        currBlock.TransferCmd = new GotoCmd(Token.NoToken, new List<Block> { nblk, afBlk });
                        newBlocks1.Add(currBlock);
                        newBlocks1.Add(afBlk);

                        nblk.Cmds.Add(ccmd);

                        callContinueBlocks.Add(nblk.Label);

                        currBlock = nblk;
                        continue;
                    }

                    currBlock.Cmds.Add(cmd);
                }

                currBlock.TransferCmd = blk.TransferCmd;
                newBlocks1.Add(currBlock);
            }

            mainCopy.Blocks = newBlocks1;
            mainCopy.Blocks.AddRange(newBlocks2);

            implToFirstBlock.Iter(kvp => firstBlockToImpl.Add(kvp.Value.Label, kvp.Key));

            if (!disableLoops)
            {
                // Get rid of loops in main
                var l2b = BoogieUtil.labelBlockMapping(mainCopy);
                foreach (var b in mainCopy.Blocks)
                {
                    var tc = b.TransferCmd as GotoCmd;
                    if (tc == null) continue;
                    tc.labelTargets = new List<Block>(tc.labelNames.Select(s => l2b[s]));
                }

                mainCopy.Blocks = LoopUnroll.UnrollLoops(mainCopy.Blocks[0], CommandLineOptions.Clo.RecursionBound, false);

                // detect loops
                l2b = BoogieUtil.labelBlockMapping(mainCopy);
                var color = new Dictionary<Block, int>();
                mainCopy.Blocks.Iter(b => color.Add(b, 0));
                var Succ = new Func<Block, IEnumerable<Block>>(b =>
                {
                    var succ = new List<Block>();
                    var gc = b.TransferCmd as GotoCmd;
                    if (gc == null) return succ;
                    gc.labelNames.Iter(s => succ.Add(l2b[s]));
                    return succ;
                });
                var parentTree = new Dictionary<Block, Block>();
                var cycle = new List<Block>();
                // DFS
                try
                {
                    DFS(mainCopy.Blocks[0], null, Succ, color, parentTree, cycle);
                }
                catch (Exception)
                {
                    var firstBlockToImpl = new Dictionary<string, string>();
                    implToFirstBlock.Iter(kvp => firstBlockToImpl.Add(kvp.Value.Label, kvp.Key));

                    cycle.Reverse();
                    cycle.Where(b => firstBlockToImpl.ContainsKey(b.Label))
                        .Iter(b => Console.WriteLine("{0}", firstBlockToImpl[b.Label]));
                    throw;
                }
            }

            // Add new main back to the program
            program.AddTopLevelDeclaration(mainCopy);
            program.mainProcName = mainCopy.Name;

            // add decl for newmain
            var origMainDecl = program.TopLevelDeclarations.OfType<Procedure>()
                .Where(proc => proc.Name == mainName)
                .FirstOrDefault();
            var newMainDecl = (new Duplicator()).VisitProcedure(origMainDecl);
            newMainDecl.Name = mainCopy.Name;
            mainCopy.Proc = newMainDecl;
            program.AddTopLevelDeclaration(newMainDecl);

            if (disableLoops)
            {
                // need to get loops out of main
                program = new CBAProgram(BoogieUtil.ReResolve(program), program.mainProcName, program.contextBound);
                var ex = new ExtractLoopsPass(true);
                program = ex.runCBAPass(program);
                // redo IDs
                (new AddUniqueCallIds()).VisitProgram(program);
                return program;
            }

            return program;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            // undo loop unrolling
            trace = LoopUnrollingPass.undoUnrolling(trace);

            // This transformation is: rename blocks, instrument calls, instrument assertions
            var ret = mapBackTraceRec(trace, 0, origMain);
            //PrintProgramPath.print(input, ret, "tr");
            return ret;
        }

        private ErrorTrace mapBackTraceRec(ErrorTrace trace, int currBlockNum, string procName)
        {
            var ret = new ErrorTrace(procName);
            var first = true;

            while (currBlockNum < trace.Blocks.Count)
            {
                var currBlock = trace.Blocks[currBlockNum];

                if (!first && firstBlockToImpl.ContainsKey(currBlock.blockName))
                {
                    var callee = firstBlockToImpl[currBlock.blockName];
                    var calleeTrace = mapBackTraceRec(trace, currBlockNum, callee);
                    var blk = ret.Blocks.Last();
                    blk.Cmds.Add(new CallInstr(calleeTrace));
                    return ret;
                }

                // what kind of block is this?
                if (blockToOrig.ContainsKey(currBlock.blockName))
                {
                    Debug.Assert(blockToOrig[currBlock.blockName].Item2 == ret.procName);
                    var blk = new ErrorTraceBlock(blockToOrig[currBlock.blockName].Item1);
                    currBlock.Cmds.Iter(c => blk.Cmds.Add(c));
                    ret.Blocks.Add(blk);
                }
                else if (assertContinueBlocks.Contains(currBlock.blockName))
                {
                    var blk = ret.Blocks.Last();
                    currBlock.Cmds.Iter(c => blk.Cmds.Add(c));
                }
                else if (callContinueBlocks.Contains(currBlock.blockName))
                {
                    var blk = ret.Blocks.Last();
                    currBlock.Cmds.Iter(c => blk.Cmds.Add(c));
                }
                else if (exitBlocks.Contains(currBlock.blockName))
                {
                    var blk = ret.Blocks.Last();
                    currBlock.Cmds.Iter(c => blk.Cmds.Add(c));
                }
                else if (callInlinedBlocks.Contains(currBlock.blockName))
                {
                    // skip this block
                }
                else
                {
                    Debug.Assert(false);
                }

                currBlockNum++;
                first = false;
            }
            return ret;
        }

        // Maps block label to the procedure that it come from,
        // when it is the entry block of that procedure
        public string EntryBlockToProc(string blockLabel)
        {
            var label = LoopUnroll.sanitizeLabel(blockLabel);
            if (!firstBlockToImpl.ContainsKey(label))
                return null;
            return firstBlockToImpl[label];
        }

        private static void DFS(Block root, Block parent, Func<Block, IEnumerable<Block>> Succ, Dictionary<Block, int> color, Dictionary<Block, Block> parentTree, List<Block> cycle)
        {
            if (color[root] == 2)
                return;

            if (color[root] == 1)
            {
                Console.WriteLine("Cycle found");
                while (root != parent)
                {
                    cycle.Add(parent);
                    parent = parentTree[parent];
                }
                cycle.Add(root);
                throw new Exception("");
            }

            parentTree[root] = parent;

            color[root] = 1;

            var succs = Succ(root);
            foreach (var s in succs)
                DFS(s, root, Succ, color, parentTree, cycle);

            color[root] = 2;
        }


        // Rename basic blocks, local variables
        // Add "havoc locals" at the beginning
        // block return
        private void RenameImpl(Implementation impl)
        {
            var origImpl = (new FixedDuplicator(true)).VisitImplementation(impl);
            var origBlocks = BoogieUtil.labelBlockMapping(origImpl);

            // create new locals
            var newLocals = new Dictionary<string, Variable>();
            foreach (var l in impl.LocVars.Concat(impl.InParams).Concat(impl.OutParams))
            {
                // substitute even formal variables with LocalVariables. This is fine
                // because we finally just merge all implemnetations together
                var nl = BoogieAstFactory.MkLocal(l.Name + "_" + impl.Name + "_copy", l.TypedIdent.Type);
                newLocals.Add(l.Name, nl);
            }

            // rename locals
            var subst = new VarSubstituter(newLocals, new Dictionary<string, Variable>());
            subst.VisitImplementation(impl);

            // Rename blocks 
            foreach (var blk in impl.Blocks)
            {
                var newName = impl.Name + "_" + blk.Label;
                blockToOrig.Add(newName, Tuple.Create(origBlocks[blk.Label].Label, origImpl.Name));
                blk.Label = newName;

                if (blk.TransferCmd is GotoCmd)
                {
                    var gc = blk.TransferCmd as GotoCmd;
                    gc.labelNames = new List<string>(
                        gc.labelNames.Select(lab => impl.Name + "_" + lab));
                }

                if (blk.TransferCmd is ReturnCmd)
                {
                    // block return
                    blk.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                }
            }

            /*
            // havoc locals -- not necessary
            if (newLocals.Count > 0)
            {
                var ies = new List<IdentifierExpr>();
                newLocals.Values.Iter(v => ies.Add(Expr.Ident(v)));
                impl.Blocks[0].Cmds.Insert(0, new HavocCmd(Token.NoToken, ies));
            }
             */
        }

        // Instrument deep asserts in a trace
        public static PersistentCBAProgram InstrumentTrace(PersistentCBAProgram ptrace, GlobalRefinementState refinementState)
        {
            var program = ptrace.getProgram();
            var main = BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, ptrace.mainProcName);

            var av = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
                "DA_assertVar", Microsoft.Boogie.Type.Bool));

            // convert "assert e" to "DA_assertVar := e"
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    for (int i = 0; i < blk.Cmds.Count; i++)
                    {
                        if (blk.Cmds[i] is AssertCmd && !BoogieUtil.isAssertTrue(blk.Cmds[i]))
                        {
                            blk.Cmds[i] = BoogieAstFactory.MkVarEqExpr(av, (blk.Cmds[i] as AssertCmd).Expr);
                        }
                    }

                }
            }

            // DA_assertVar := true
            var sblk = new Block(Token.NoToken, "newMainStartBlk__0", new List<Cmd>(),
                BoogieAstFactory.MkGotoCmd(main.Blocks[0].Label));

            sblk.Cmds.Add(BoogieAstFactory.MkVarEqConst(av, true));
            var nblks = main.Blocks;
            main.Blocks = new List<Block>();
            main.Blocks.Add(sblk);
            main.Blocks.AddRange(nblks);

            // assert DA_assertVar
            main.Blocks.Where(blk => blk.TransferCmd is ReturnCmd)
                .Iter(blk => blk.Cmds.Add(BoogieAstFactory.MkAssert(Expr.Ident(av))));

            program.AddTopLevelDeclaration(av);
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl => impl.Proc.Modifies.Add(Expr.Ident(av)));

            // Reflect the addition of a new global variable on
            // our refinement state
            refinementState.Add(new AddVarMapping(new VarSet(av.Name, "")));

            return new PersistentCBAProgram(program, ptrace.mainProcName, ptrace.contextBound);
        }

        // Inverse for InstrumentTrace
        public ErrorTrace InstrumentTraceMapBack(ErrorTrace trace)
        {
            // get rid of first block of main and the last assert
            Debug.Assert(trace.Blocks[0].blockName == "newMainStartBlk__0");
            trace.Blocks.RemoveAt(0);
            var lastBlk = trace.Blocks.Last();
            lastBlk.Cmds.RemoveAt(lastBlk.Cmds.Count - 1);
            return trace;
        }
    }

    /* TODO: Unify with DeepAssertRewrite */
    public class ConcurrentDeepAssertRewrite : CompilerPass
    {
        public string newMainName;
        public HashSet<string> newVars;

        Dictionary<string, string> firstBlockToImpl;

        // newBlock -> <origBlock, Proc>
        Dictionary<string, Tuple<string, string>> blockToOrig;

        // continue blocks
        HashSet<string> assertContinueBlocks;
        HashSet<string> callContinueBlocks;

        public ConcurrentDeepAssertRewrite()
        {
            newMainName = null;
            firstBlockToImpl = new Dictionary<string, string>();
            blockToOrig = new Dictionary<string, Tuple<string, string>>();
            assertContinueBlocks = new HashSet<string>();
            callContinueBlocks = new HashSet<string>();
            newVars = new HashSet<string>();
        }

        public override CBAProgram runCBAPass(CBAProgram program)
        {
            // Identify main
            var main = program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint") ||
                    QKeyValue.FindBoolAttribute(impl.Proc.Attributes, "entrypoint"))
                .FirstOrDefault();
            if (main == null && program.mainProcName != null)
                main = BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, program.mainProcName);
            if (main.OutParams.Count != 0)
            {
                // create a dummy main that calls the original one
                main = CreateDummyMain(program, main);
                program.mainProcName = main.Name;
            }
            SequentialInstrumentation.isSingleThreadProgram(program, main.Name);

            // Prepare for stratified inlining with assertions
            var procsThatCannotReachAssert = new HashSet<string>();
            program.TopLevelDeclarations.OfType<Procedure>().Iter(proc => procsThatCannotReachAssert.Add(proc.Name));
            procsThatCannotReachAssert.ExceptWith(procsThatCanSequentiallyReachAsserts(program));

            //if (procsThatCannotReachAssert.Contains(program.mainProcName))
            //    return program;

            // loopy guys cannot reach asserts
            program.TopLevelDeclarations.OfType<LoopProcedure>()
                .Iter(proc => procsThatCannotReachAssert.Add(proc.Name));

            program.TopLevelDeclarations.OfType<Procedure>()
                .Where(proc => QKeyValue.FindBoolAttribute(proc.Attributes, "LoopProcedure"))
                .Iter(proc => procsThatCannotReachAssert.Add(proc.Name));

            // Make copies of all procedures that can reach assert
            var implCopy = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => !procsThatCannotReachAssert.Contains(impl.Name))
                .Iter(impl => implCopy.Add(impl.Name,
                    (new FixedDuplicator(true)).VisitImplementation(impl)));

            // Disable assertions in the original procedures
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl =>
                    impl.Blocks.Iter(blk =>
                    {
                        for (int i = 0; i < blk.Cmds.Count; i++)
                        {
                            var ac = blk.Cmds[i] as AssertCmd;
                            if (ac != null) blk.Cmds[i] = new AssumeCmd(ac.tok, ac.Expr);
                        }
                    }));


            // async procs
            var asyncProcs = new HashSet<string>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .Iter(impl => impl.Blocks
                    .Iter(blk => blk.Cmds.OfType<CallCmd>()
                        .Where(c => c.IsAsync)
                        .Iter(c => asyncProcs.Add(c.callee))));
            asyncProcs.Add(main.Name);

            // flag
            var flag = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
                "daFlag", Microsoft.Boogie.Type.Int));
            // proc To Num
            var procToNum = new Dictionary<string, int>();
            foreach (var p in asyncProcs)
                procToNum.Add(p, procToNum.Count + 1);
            newVars.Add(flag.Name);

            // constants for arguments
            var argConstants = new Dictionary<Microsoft.Boogie.Type, List<Constant>>();
            var argCnt = 0;
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>().Where(i => asyncProcs.Contains(i.Name)))
            {
                var myCnt = new Dictionary<Microsoft.Boogie.Type, int>();
                foreach (var v in impl.InParams)
                {
                    var vType = v.TypedIdent.Type;
                    if (!myCnt.ContainsKey(vType))
                    {
                        myCnt[vType] = 0;
                    }
                    if (!argConstants.ContainsKey(vType))
                    {
                        argConstants[vType] = new List<Constant>();
                    }
                    if (argConstants[vType].Count == myCnt[vType])
                    {
                        argConstants[vType].Add(new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "daArg" + argCnt.ToString(), vType)));
                        argCnt++;
                    }
                    myCnt[vType] = myCnt[vType] + 1;
                }
            }
            Console.WriteLine("Creating {0} constants for async proc arguments", argCnt);

            var mainName = main.Name;

            // delete entrypoint attribute
            main.Attributes = BoogieUtil.removeAttr("entrypoint", main.Attributes);
            main.Proc.Attributes = BoogieUtil.removeAttr("entrypoint", main.Proc.Attributes);

            // create a new main
            var newMainProc = new Procedure(Token.NoToken, "daFakeMain", new List<TypeVariable>(main.Proc.TypeParameters),
                new List<Variable>(main.Proc.InParams), new List<Variable>(main.Proc.OutParams), new List<Requires>(main.Proc.Requires),
                new List<IdentifierExpr>(), new List<Ensures>(main.Proc.Ensures));

            var newMainImpl = new Implementation(Token.NoToken, "daFakeMain", new List<TypeVariable>(main.TypeParameters),
                new List<Variable>(main.InParams), new List<Variable>(main.OutParams), new List<Variable>(), new List<Block>());

            newMainImpl.AddAttribute("entrypoint");
            newMainProc.AddAttribute("entrypoint");
            newMainName = newMainImpl.Name;

            // rename stuff
            implCopy.Values
                .Iter(impl => RenameImpl(impl));

            // Add all procedures to main
            var implToFirstBlock = new Dictionary<string, Block>();
            implCopy.Values
                .Iter(impl => implToFirstBlock.Add(impl.Name, impl.Blocks[0]));

            // Merge impls
            foreach (var impl in implCopy.Values)
            {
                // union locals
                newMainImpl.LocVars.AddRange(impl.LocVars);
                // formals have already been substituted by locals
                newMainImpl.LocVars.AddRange(impl.OutParams);
                newMainImpl.LocVars.AddRange(impl.InParams);

                newMainImpl.Blocks.AddRange(impl.Blocks);
            }

            // Block return in main
            foreach (var blk in newMainImpl.Blocks.Where(b => b.TransferCmd is ReturnCmd))
                blk.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));

            // Edit procedure calls in the copied impls
            var newLabCnt = 0;
            var GetNewLabel = new Func<string>(() =>
            {
                return "sia_lab" + (newLabCnt++);
            });

            var GetExitBlock = new Func<Block>(() =>
                new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(), new ReturnCmd(Token.NoToken)));

            var newBlocks1 = new List<Block>();
            var newBlocks2 = new List<Block>();

            foreach (var blk in newMainImpl.Blocks)
            {
                var currBlock = new Block(blk.tok, blk.Label, new List<Cmd>(), null);

                foreach (var cmd in blk.Cmds)
                {
                    var ccmd = cmd as CallCmd;
                    if (ccmd != null && implToFirstBlock.ContainsKey(ccmd.callee) && !ccmd.IsAsync)
                    {
                        var lab = GetNewLabel();
                        var afBlk = new Block(Token.NoToken, lab, new List<Cmd>(), BoogieAstFactory.MkGotoCmd(implToFirstBlock[ccmd.callee].Label));

                        // formal-in := actuals
                        for (int i = 0; i < implCopy[ccmd.callee].InParams.Count; i++)
                        {
                            var formal = implCopy[ccmd.callee].InParams[i];
                            var actual = ccmd.Ins[i];
                            afBlk.Cmds.Add(BoogieAstFactory.MkVarEqExpr(formal, actual));
                        }

                        lab = GetNewLabel();
                        var nblk = new Block(Token.NoToken, lab, new List<Cmd>(), null);

                        // Finish current block
                        currBlock.TransferCmd = new GotoCmd(Token.NoToken, new List<Block> { nblk, afBlk });
                        newBlocks1.Add(currBlock);
                        newBlocks1.Add(afBlk);

                        nblk.Cmds.Add(ccmd);

                        currBlock = nblk;
                        continue;
                    }
                    currBlock.Cmds.Add(cmd);
                }

                currBlock.TransferCmd = blk.TransferCmd;
                newBlocks1.Add(currBlock);
            }

            newMainImpl.Blocks = newBlocks1;
            newMainImpl.Blocks.AddRange(newBlocks2);

            implToFirstBlock.Iter(kvp => firstBlockToImpl.Add(kvp.Value.Label, kvp.Key));

            // add preamble for the new main
            //   flag := 0
            //   if(*)
            //      async main() && dispatch to thread entries on flag
            //   else
            //      flag := main && goto main

            var mainCanFail = !procsThatCannotReachAssert.Contains(main.Name);
            var threadEntryBlocks = new Dictionary<string, Block>();
            foreach (var p in asyncProcs)
            {
                if (!implToFirstBlock.ContainsKey(p))
                    continue;

                var blk = new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(), BoogieAstFactory.MkGotoCmd(implToFirstBlock[p].Label));
                var pcopy = implCopy[p];
                var myCnt = new Dictionary<Microsoft.Boogie.Type, int>();
                foreach (var v in pcopy.InParams)
                {
                    var vType = v.TypedIdent.Type;
                    if (!myCnt.ContainsKey(vType))
                    {
                        myCnt[vType] = 0;
                    }
                    var idx = myCnt[vType];
                    blk.Cmds.Add(BoogieAstFactory.MkAssumeVarEqVar(v, argConstants[vType][idx]));
                    myCnt[vType] = idx + 1;
                }
                blk.Cmds.Add(BoogieAstFactory.MkAssumeVarEqConst(flag, procToNum[p]));
                threadEntryBlocks.Add(p, blk);
            }
            var sb2 = new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(),
                mainCanFail ? BoogieAstFactory.MkGotoCmd(threadEntryBlocks[main.Name].Label) as TransferCmd : new ReturnCmd(Token.NoToken));
            if (mainCanFail)
            {
                sb2.Cmds.Add(BoogieAstFactory.MkVarEqConst(flag, procToNum[main.Name]));
            }
            var gcAll = new GotoCmd(Token.NoToken, new List<string>(threadEntryBlocks.Where(kvp => kvp.Key != main.Name)
                    .Select(kvp => kvp.Value.Label))) as TransferCmd;
            if ((gcAll as GotoCmd).labelNames.Count == 0)
                gcAll = new ReturnCmd(Token.NoToken);

            var sb3 = new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(),
                gcAll);
            sb3.Cmds.Add(new CallCmd(Token.NoToken, main.Name,
                new List<Expr>(newMainImpl.InParams.Select(v => Expr.Ident(v))), new List<IdentifierExpr>(newMainImpl.OutParams.Select(v => Expr.Ident(v))), null, true));

            var sb1 = new Block(Token.NoToken, GetNewLabel(), new List<Cmd>(),
                BoogieAstFactory.MkGotoCmd(sb2.Label, sb3.Label));
            sb1.Cmds.Add(BoogieAstFactory.MkVarEqConst(flag, 0));


            var nb = new List<Block>();
            nb.Add(sb1); nb.Add(sb2); nb.Add(sb3);
            nb.AddRange(threadEntryBlocks.Values);
            nb.AddRange(newMainImpl.Blocks);
            newMainImpl.Blocks = nb;

            program.AddTopLevelDeclaration(flag);
            foreach (var cnsts in argConstants.Values)
            {
                program.AddTopLevelDeclarations(cnsts);
            }

            // Instrument async in original procedures
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                var newBlocks = new List<Block>();

                foreach (var blk in impl.Blocks)
                {
                    var currCmds = new List<Cmd>();
                    var currLabel = blk.Label;

                    foreach (var cmd in blk.Cmds)
                    {
                        var ccmd = cmd as CallCmd;
                        if (ccmd == null || !ccmd.IsAsync || !implToFirstBlock.ContainsKey(ccmd.callee))
                        {
                            currCmds.Add(cmd);
                            continue;
                        }
                        var lab1 = GetNewLabel();
                        var lab2 = GetNewLabel();
                        var lab3 = GetNewLabel();

                        // end current block
                        newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds,
                            BoogieAstFactory.MkGotoCmd(lab1, lab2)));

                        // lab1: set args; flag := T; goto lab3;
                        var cmds1 = new List<Cmd>();
                        var myCnt = new Dictionary<Microsoft.Boogie.Type, int>();
                        for (int i = 0; i < ccmd.Ins.Count; i++)
                        {
                            var vType = ccmd.Proc.InParams[i].TypedIdent.Type;
                            if (!myCnt.ContainsKey(vType))
                            {
                                myCnt[vType] = 0;
                            }
                            var idx = myCnt[vType];
                            cmds1.Add(BoogieAstFactory.MkAssume(Expr.Eq(ccmd.Ins[i], Expr.Ident(argConstants[vType][idx]))));
                            myCnt[vType] = idx + 1;
                        }
                        cmds1.Add(BoogieAstFactory.MkVarEqConst(flag, procToNum[ccmd.callee]));
                        newBlocks.Add(new Block(Token.NoToken, lab1, cmds1, 
                            BoogieAstFactory.MkGotoCmd(lab3)));

                        // lab2: ccmd
                        newBlocks.Add(new Block(Token.NoToken, lab2, new List<Cmd>{ccmd},
                            BoogieAstFactory.MkGotoCmd(lab3)));

                        currLabel = lab3;
                        currCmds = new List<Cmd>();
                    }
                    newBlocks.Add(new Block(Token.NoToken, currLabel, currCmds,
                        blk.TransferCmd));
                }
                impl.Blocks = newBlocks;
            }

            // detect loops
            var l2b = BoogieUtil.labelBlockMapping(newMainImpl);
            var color = new Dictionary<Block, int>();
            newMainImpl.Blocks.Iter(b => color.Add(b, 0));
            var Succ = new Func<Block, IEnumerable<Block>>(b =>
            {
                var succ = new List<Block>();
                var gc = b.TransferCmd as GotoCmd;
                if (gc == null) return succ;
                gc.labelNames.Iter(s => succ.Add(l2b[s]));
                return succ;
            });
            var parentTree = new Dictionary<Block, Block>();
            var cycle = new List<Block>();
            // DFS
            try
            {
                DFS(newMainImpl.Blocks[0], null, Succ, color, parentTree, cycle);
            }
            catch (Exception)
            {
                var firstBlockToImpl = new Dictionary<string, string>();
                implToFirstBlock.Iter(kvp => firstBlockToImpl.Add(kvp.Value.Label, kvp.Key));

                cycle.Reverse();
                cycle.Where(b => firstBlockToImpl.ContainsKey(b.Label))
                    .Iter(b => Console.WriteLine("{0}", firstBlockToImpl[b.Label]));
                throw;
            }

            var bwa = new HashSet<Block>();
            newMainImpl.Blocks
                .Where(blk => blk.Cmds.OfType<AssertCmd>()
                    .Any(c => !BoogieUtil.isAssertTrue(c)))
                .Iter(blk => bwa.Add(blk));
            if (bwa.All(b => color[b] == 0))
            {
                Console.WriteLine("Assert statically not reachable");
            }
                    
            // Add new main back to the program
            program.AddTopLevelDeclaration(newMainImpl);

            // add decl for newmain
            newMainImpl.Proc = newMainProc;
            program.AddTopLevelDeclaration(newMainProc);
            program.mainProcName = newMainName;

            return program;
        }

        private Implementation CreateDummyMain(Program program, Implementation main) 
        {
            var dup = new FixedDuplicator();
            var newMain = dup.VisitImplementation(main);
            var newProc = dup.VisitProcedure(main.Proc);

            newMain.Name = "DA_dummy_" + main.Name;
            newProc.Name = "DA_dummy_" + main.Name;
            newMain.Proc = newProc;

            // drop out params -- make them locals
            newMain.LocVars = new List<Variable>();
            newMain.LocVars.AddRange(newMain.OutParams);
            newMain.OutParams = new List<Variable>();
            newProc.OutParams = new List<Variable>();

            var mainIns = new List<Expr>();
            foreach (Variable v in newMain.InParams)
            {
                mainIns.Add(Expr.Ident(v));
            }
            var mainOuts = new List<IdentifierExpr>();
            foreach (Variable v in newMain.LocVars)
            {
                mainOuts.Add(Expr.Ident(v));
            }

            var callMain = new CallCmd(Token.NoToken, main.Name, mainIns, mainOuts);
            callMain.Proc = main.Proc;

            var blk = new Block(Token.NoToken, "start", new List<Cmd>{callMain}, new ReturnCmd(Token.NoToken));
            newMain.Blocks = new List<Block>();
            newMain.Blocks.Add(blk);

            program.AddTopLevelDeclaration(newProc);
            program.AddTopLevelDeclaration(newMain);

            // Set entrypoint
            main.Attributes = BoogieUtil.removeAttr("entrypoint", main.Attributes);
            main.Proc.Attributes = BoogieUtil.removeAttr("entrypoint", main.Proc.Attributes);

            newMain.AddAttribute("entrypoint");
            newMain.Proc.AddAttribute("entrypoint");

            return newMain;
        }


        public static HashSet<string> procsThatCanSequentiallyReachAsserts(Program program)
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
                    foreach (var cmd in blk.Cmds.OfType<CallCmd>().Where(c => !c.IsAsync))
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


        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            throw new NotImplementedException();
        }

        private static void DFS(Block root, Block parent, Func<Block, IEnumerable<Block>> Succ, Dictionary<Block, int> color, Dictionary<Block, Block> parentTree, List<Block> cycle)
        {
            if (color[root] == 2)
                return;

            if (color[root] == 1)
            {
                Console.WriteLine("Cycle found");
                while (root != parent)
                {
                    cycle.Add(parent);
                    parent = parentTree[parent];
                }
                cycle.Add(root);
                throw new Exception("");
            }

            parentTree[root] = parent;

            color[root] = 1;

            var succs = Succ(root);
            foreach (var s in succs)
                DFS(s, root, Succ, color, parentTree, cycle);

            color[root] = 2;
        }


        // Rename basic blocks, local variables
        // Add "havoc locals" at the beginning
        // block return
        private void RenameImpl(Implementation impl)
        {
            var origImpl = (new FixedDuplicator(true)).VisitImplementation(impl);
            var origBlocks = BoogieUtil.labelBlockMapping(origImpl);

            // create new locals
            var newLocals = new Dictionary<string, Variable>();
            foreach (var l in impl.LocVars.Concat(impl.InParams).Concat(impl.OutParams))
            {
                // substitute even formal variables with LocalVariables. This is fine
                // because we finally just merge all implemnetations together
                var nl = BoogieAstFactory.MkLocal(l.Name + "_" + impl.Name + "_copy", l.TypedIdent.Type);
                newLocals.Add(l.Name, nl);
            }

            // rename locals
            var subst = new VarSubstituter(newLocals, new Dictionary<string, Variable>());
            subst.VisitImplementation(impl);

            // Rename blocks 
            foreach (var blk in impl.Blocks)
            {
                var newName = impl.Name + "_" + blk.Label;
                blockToOrig.Add(newName, Tuple.Create(origBlocks[blk.Label].Label, origImpl.Name));
                blk.Label = newName;

                if (blk.TransferCmd is GotoCmd)
                {
                    var gc = blk.TransferCmd as GotoCmd;
                    gc.labelNames = new List<string>(
                        gc.labelNames.Select(lab => impl.Name + "_" + lab));
                }

                if (blk.TransferCmd is ReturnCmd)
                {
                    // block return
                    blk.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                }
            }

            /*
            // havoc locals -- not necessary
            if (newLocals.Count > 0)
            {
                var ies = new List<IdentifierExpr>();
                newLocals.Values.Iter(v => ies.Add(Expr.Ident(v)));
                impl.Blocks[0].Cmds.Insert(0, new HavocCmd(Token.NoToken, ies));
            }
             */
        }

    }

}

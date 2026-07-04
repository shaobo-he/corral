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

        private CBAProgram feedToBoogie(CBAProgram p)
        {
            // Do typechecking 
            if (BoogieUtil.TypecheckProgram(p as Program, "verificationPass"))
            {
                BoogieUtil.PrintProgram(p, "error.bpl");
                throw new InvalidProg("Cannot typecheck");
            }

            BoogieVerify.options.Set();

            // An important pass for recording the value of int variables
            Debug.Assert(CommandLineOptions.Clo.StratifiedInlining > 0);
            if (WillGetModel)
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

                if (prune != null) etrace = prune.mapBackTrace(etrace);
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
                            rc = new CallCmd(Token.NoToken, recordIntArgProc, new List<Expr> { Expr.Ident(v) }, new List<IdentifierExpr>());
                            rc.Proc = intDecl;
                        }
                        else
                        {
                            rc = new CallCmd(Token.NoToken, recordBoolArgProc, new List<Expr> { Expr.Ident(v) }, new List<IdentifierExpr>());
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
            if (btrace == null) return null;

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
            if (compressBlocks != null)
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
            if (compressBlocks != null)
                trace = compressBlocks.mapBackTrace(trace);
            return varEliminator.mapBackTrace(trace);

            //return trace;
        }
    }


}

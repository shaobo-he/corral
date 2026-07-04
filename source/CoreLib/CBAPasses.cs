using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;
using Microsoft.Boogie.GraphUtil;

namespace cba
{
    // This is used for pre-processing of the input program. We rewrite calls
    // so that they only operate on local variables.
    public class RewriteCallCmdsPass : CompilerPass
    {
        RewriteCallCmds rcc;

        public RewriteCallCmdsPass()
        {
            rcc = new RewriteCallCmds(false);
            passName = "Rewriting calls";
        }

        public RewriteCallCmdsPass(bool rewriteAll)
        {
            rcc = new RewriteCallCmds(!rewriteAll);
            passName = "Rewriting calls";
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            rcc.VisitProgram(p as Program);
            return p;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return rcc.tinfo.mapBackTrace(trace);
        }
    }

    // This is used for pre-processing of the input program. We rewrite asserts
    // so that we know which one of them failed.
    public class RewriteAssertsPass : CompilerPass
    {
        RewriteAsserts rcc;

        public RewriteAssertsPass()
        {
            rcc = new RewriteAsserts();
            passName = "Rewriting asserts";
        }

        public RewriteAssertsPass(bool shouldFindAssert)
        {
            rcc = new RewriteAsserts(shouldFindAssert);
            passName = "Rewriting asserts";
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            rcc.VisitProgram(p as Program);
            return p;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return rcc.mapBackTrace(trace);
        }

        public AssertLocation getFailingAssertLocation()
        {
            return rcc.failingAssert;
        }

        // found assert?
        public bool foundAssert
        {
            get
            {
                return rcc.assertFound;
            }
        }

        // For allowing multiple traces to be mapped back
        public void reset()
        {
            rcc.reset();
        }

    }

    public class AddUniqueCallIds
    {
        private static int counter = 0;
        public static bool useGlobalCounter = true;
        // (caller, callee, int) -> (block label, cnt)
        public Dictionary<Tuple<string, string, int>, Tuple<string, int>> callIdToLocation;

        public AddUniqueCallIds()
        {
            callIdToLocation = new Dictionary<Tuple<string, string, int>, Tuple<string, int>>();
        }

        public void VisitProgram(Program program)
        {
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
                VisitImplementation(impl);
        }

        public void VisitImplementation(Implementation impl)
        {
            // callee -> id
            var cnt = new Dictionary<string, int>();

            foreach (var block in impl.Blocks)
            {
                var callcnt = 0;
                for (int i = 0; i < block.Cmds.Count; i++)
                {
                    var cc = block.Cmds[i] as CallCmd;
                    if (cc == null) continue;

                    if (!cnt.ContainsKey(cc.callee))
                        cnt[cc.callee] = 0;

                    var uniqueId = useGlobalCounter ? counter : cnt[cc.callee];
                    var attr = new List<object>();
                    attr.Add(new LiteralExpr(Token.NoToken, Microsoft.BaseTypes.BigNum.FromInt(uniqueId)));

                    cc.Attributes = BoogieUtil.removeAttr("si_old_unique_call", cc.Attributes);
                    var oldAttr = BoogieUtil.getAttr("si_unique_call", cc.Attributes);
                    if (oldAttr != null)
                    {
                        cc.Attributes = BoogieUtil.removeAttr("si_unique_call", cc.Attributes);
                        var newattr = new QKeyValue(Token.NoToken, "si_old_unique_call", oldAttr, null);
                        if (cc.Attributes == null)
                            cc.Attributes = newattr;
                        else
                            cc.Attributes.AddLast(newattr);
                    }

                    cc.Attributes = new QKeyValue(Token.NoToken, "si_unique_call", attr, cc.Attributes);
                    callIdToLocation.Add(Tuple.Create(impl.Name, cc.callee, uniqueId), Tuple.Create(block.Label, callcnt));

                    cnt[cc.callee]++;

                    callcnt++;
                    counter++;
                }
            }

        }

    }

    public class ExtractLoopsPass : LoopUnrollingPass
    {
        // proc name -> new block name -> orig block name
        Dictionary<string, Dictionary<string, string>> info;

        HashSet<string> allProcs;
        HashSet<string> loopProcs;

        bool addUniqueCallLabels;

        public ExtractLoopsPass()
            : base(-1)
        {
            info = null;
            addUniqueCallLabels = false;
        }

        public ExtractLoopsPass(bool addUniqueCallLabels)
            : base(-1)
        {
            info = null;
            this.addUniqueCallLabels = addUniqueCallLabels;
        }


        public ExtractLoopsPass(int n)
            : base(n)
        {
            info = null;
            this.addUniqueCallLabels = false;
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            if (unrollNum >= 0)
            {
                return base.runCBAPass(p);
            }

            foreach (var impl in BoogieUtil.GetImplementations(p))
            {
                impl.PruneUnreachableBlocks(BoogieUtil.BoogieOptions);
            }

            // save RB
            var rb = BoogieUtil.RecursionBound;
            if (BoogieVerify.irreducibleLoopUnroll >= 0)
                BoogieUtil.RecursionBound = BoogieVerify.irreducibleLoopUnroll;

            var procsWithIrreducibleLoops = new HashSet<string>();
            var passInfo = LoopExtractor.ExtractLoops(BoogieUtil.BoogieOptions, p);
            BoogieUtil.ResolveProgram(p);
            BoogieUtil.TypecheckProgram(p);

            // restore RB
            BoogieUtil.RecursionBound = rb;

            // no loops found, then this transformation is identity
            if (passInfo.Count == 0 && procsWithIrreducibleLoops.Count == 0)
                return null;

            if (addUniqueCallLabels)
            {
                // annotate calls with a unique number
                var addIds = new AddUniqueCallIds();

                // Loop unrolling is done for procs with irreducible loops.
                // This simply copies Cmd objects. Duplicate them to remove
                // aliasing
                foreach (var impl in p.TopLevelDeclarations
                    .OfType<Implementation>()
                    .Where(impl => procsWithIrreducibleLoops.Contains(impl.Name)))
                {
                    var dup = new FixedDuplicator(true);
                    foreach (var blk in impl.Blocks)
                    {
                        blk.Cmds = dup.VisitCmdSeq(blk.Cmds);
                    }
                }

                // Add labels again to all procedures
                foreach (var impl in p.TopLevelDeclarations
                    .OfType<Implementation>())
                    addIds.VisitImplementation(impl);
            }

            info = new Dictionary<string, Dictionary<string, string>>();
            passInfo.Iter(kvp =>
                {
                    info.Add(kvp.Key, new Dictionary<string, string>());
                    kvp.Value.Iter(sb => info[kvp.Key].Add(sb.Key, sb.Value.Label));
                });

            // Construct the set of procs in the original program
            // and the loop procedures
            allProcs = new HashSet<string>();
            loopProcs = new HashSet<string>();
            foreach (var decl in p.TopLevelDeclarations)
            {
                var impl = decl as Implementation;
                if (impl == null) continue;
                allProcs.Add(impl.Name);
                if (impl.Proc is LoopProcedure)
                {
                    loopProcs.Add(impl.Name);
                    impl.Proc.AddAttribute("LoopProcedure");
                }
            }

            //foreach (var impl in BoogieUtil.GetImplementations(p))
            //{
            //removeAssumeFalseBlocks(impl);
            //}


            // Optimization: if no loop is found, then no need to print
            // out a new program
            if (loopProcs.Count == 0)
                return null;

            // Remove vars from attributes that are not in scope anymore
            RemoveVarsFromAttributes.Prune(p);

            return p;
        }

        private void removeAssumeFalseBlocks(Implementation impl)
        {
            // Identify "assume false" blocks
            var afBlocks = new HashSet<string>();
            foreach (var blk in impl.Blocks)
            {
                if (blk.Cmds.Count == 0) continue;
                var acmd = blk.Cmds[0] as AssumeCmd;
                if (acmd == null) continue;
                var le = acmd.Expr as LiteralExpr;
                if (le == null) continue;
                if (le.IsFalse) { afBlocks.Add(blk.Label); }
            }

            var newBlocks = new List<Block>();
            foreach (var blk in impl.Blocks)
            {
                if (afBlocks.Contains(blk.Label)) continue;
                newBlocks.Add(blk);
                var gc = blk.TransferCmd as GotoCmd;
                if (gc == null) continue;
                var ss = new List<String>();
                foreach (var t in gc.LabelNames)
                {
                    if (afBlocks.Contains(t)) continue;
                    ss.Add(t);
                }
                if (ss.Count > 0)
                {
                    blk.TransferCmd = new GotoCmd(gc.tok, ss);
                }
                else
                {
                    blk.Cmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                    blk.TransferCmd = new ReturnCmd(Token.NoToken);
                }

            }
            impl.Blocks = newBlocks;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            if (unrollNum >= 0) return base.mapBackTrace(trace);

            var ret = new ErrorTrace(trace.procName);
            var firstInfo = trace.Blocks[0].info;
            ErrorTraceBlock lastBlk = null;

            foreach (var blk in trace.Blocks)
            {
                var rblkLabel = elGetBlock(trace.procName, blk.blockName);
                if (rblkLabel != null)
                {
                    lastBlk = new ErrorTraceBlock(rblkLabel);
                    lastBlk.info = blk.info;
                    if (ret.Blocks.Count == 0 && lastBlk.info == null) lastBlk.info = firstInfo;
                    ret.addBlock(lastBlk);
                }

                foreach (var cmd in blk.Cmds)
                {
                    var ccmd = cmd as CallInstr;
                    if (ccmd == null || ccmd.calleeTrace == null)
                    {
                        if (lastBlk != null) lastBlk.addInstr(cmd);
                        continue;
                    }
                    var ctrace = mapBackTrace(ccmd.calleeTrace);
                    if (isLoop(ctrace.procName))
                    {
                        // absorb trace
                        ret.Blocks.AddRange(ctrace.Blocks);
                        lastBlk = null;
                    }
                    else
                    {
                        if (lastBlk != null) lastBlk.addInstr(new CallInstr(ctrace.procName, ctrace, ccmd.asyncCall, cmd.info));
                        continue;
                    }
                }

            }
            if (trace.returns && ret.Blocks.Count > 0)
            {
                ret.addReturn(trace.raisesException);
            }
            return ret;
        }

        private bool isLoop(string procName)
        {
            return loopProcs.Contains(procName);
        }

        private string elGetBlock(string procname, string block)
        {
            if (!info.ContainsKey(procname))
                return block;

            if (!info[procname].ContainsKey(block))
                return null;

            return info[procname][block];
        }

    }

}

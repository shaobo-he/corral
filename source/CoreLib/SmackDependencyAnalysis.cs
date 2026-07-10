using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using cba.Util;

namespace cba
{
    public class SmackDependencyAnalysisPass : CompilerPass
    {
        private readonly ModifyTrans tinfo;

        public SmackDependencyAnalysisPass()
        {
            passName = "SMACK assertion dependency analysis";
            tinfo = new ModifyTrans();
        }

        public override CBAProgram runCBAPass(CBAProgram p)
        {
            var analysis = new SmackDependencyAnalysis(tinfo);
            analysis.Run(p);
            return p;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return tinfo.mapBackTrace(trace);
        }
    }

    internal class SmackDependencyAnalysis
    {
        private const string CheckIdAttr = "smack.check_id";
        private const string CheckKindAttr = "smack.check_kind";
        private const string CheckIdAttrCompat = "smack_check_id";
        private const string CheckKindAttrCompat = "smack_check_kind";
        private const string CoveredAttr = "smack.covered";
        private const string CoveredByAttr = "smack.covered_by";
        private const string CoveredReasonAttr = "smack.covered_reason";
        private const string LearnedAttr = "smack.learned";
        private const string LearnedFromAttr = "smack.learned_from";
        private const string SmackOverflowProc = "__SMACK_check_overflow";

        private readonly ModifyTrans tinfo;
        private readonly FixedDuplicator duplicator;
        private int totalChecks;
        private int coveredChecks;
        private readonly List<string> coverageEdges;

        public SmackDependencyAnalysis(ModifyTrans tinfo)
        {
            this.tinfo = tinfo;
            duplicator = new FixedDuplicator(true);
            coverageEdges = new List<string>();
        }

        public void Run(CBAProgram program)
        {
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                AnalyzeImplementation(impl);
            }

            Console.WriteLine("SMACK dependency analysis: {0} checks, {1} covered", totalChecks, coveredChecks);
            foreach (var edge in coverageEdges.Take(20))
            {
                Console.WriteLine("  covered {0}", edge);
            }
            if (coverageEdges.Count > 20)
            {
                Console.WriteLine("  ... {0} more covered checks", coverageEdges.Count - 20);
            }
        }

        private void AnalyzeImplementation(Implementation impl)
        {
            if (impl.Blocks.Count == 0 || !ContainsAnalyzableCheck(impl))
            {
                return;
            }

            var blockMap = impl.Blocks.ToDictionary(b => b.Label, b => b);
            var entryStates = ComputeEntryStates(impl, blockMap);
            var covered = FindCoveredAssertions(impl, entryStates);
            RewriteImplementation(impl, covered);
        }

        private static bool ContainsAnalyzableCheck(Implementation impl)
        {
            foreach (var block in impl.Blocks)
            {
                foreach (var cmd in block.Cmds)
                {
                    if (cmd is CallCmd callCmd && IsSmackOverflowCheck(callCmd))
                    {
                        return true;
                    }

                    if (impl.Name != SmackOverflowProc &&
                        cmd is AssertCmd assertCmd &&
                        IsSmackCheck(assertCmd))
                    {
                        return true;
                    }
                }
            }

            return false;
        }

        private Dictionary<string, AbstractState> ComputeEntryStates(
            Implementation impl,
            Dictionary<string, Block> blockMap)
        {
            var entry = impl.Blocks[0].Label;
            var inStates = blockMap.Keys.ToDictionary(label => label, label => (AbstractState)null);
            inStates[entry] = AbstractState.Top();

            var worklist = new Queue<string>();
            var queued = new HashSet<string>();
            worklist.Enqueue(entry);
            queued.Add(entry);

            while (worklist.Count != 0)
            {
                var label = worklist.Dequeue();
                queued.Remove(label);

                var state = inStates[label].Clone();
                TransferBlock(blockMap[label], state, impl.Name, null);

                foreach (var succ in GetSuccessors(blockMap[label]))
                {
                    if (!inStates.ContainsKey(succ))
                    {
                        continue;
                    }

                    var joined = AbstractState.Join(inStates[succ], state);
                    if (AbstractState.Same(inStates[succ], joined))
                    {
                        continue;
                    }

                    inStates[succ] = joined;
                    if (!queued.Contains(succ))
                    {
                        worklist.Enqueue(succ);
                        queued.Add(succ);
                    }
                }
            }

            return inStates;
        }

        private Dictionary<Cmd, CoverageInfo> FindCoveredAssertions(
            Implementation impl,
            Dictionary<string, AbstractState> entryStates)
        {
            var covered = new Dictionary<Cmd, CoverageInfo>();
            foreach (var block in impl.Blocks)
            {
                var state = entryStates[block.Label];
                if (state == null)
                {
                    continue;
                }

                state = state.Clone();
                TransferBlock(block, state, impl.Name, covered);
            }
            return covered;
        }

        private void TransferBlock(
            Block block,
            AbstractState state,
            string procName,
            Dictionary<Cmd, CoverageInfo> covered)
        {
            for (int i = 0; i < block.Cmds.Count; i++)
            {
                TransferCmd(block.Cmds[i], state, procName, block.Label, i, covered);
            }
        }

        private void TransferCmd(
            Cmd cmd,
            AbstractState state,
            string procName,
            string blockName,
            int cmdIndex,
            Dictionary<Cmd, CoverageInfo> covered)
        {
            if (state.IsBottom)
            {
                return;
            }

            if (cmd is AssumeCmd assumeCmd)
            {
                state.Assume(assumeCmd.Expr, "assume");
                return;
            }

            if (cmd is AssertCmd assertCmd && IsSmackCheck(assertCmd) && procName != SmackOverflowProc)
            {
                var checkId = GetCheckId(assertCmd, procName, blockName, cmdIndex);
                if (covered != null)
                {
                    totalChecks++;
                }
                if (state.Implies(assertCmd.Expr, out var reason) && covered != null)
                {
                    coveredChecks++;
                    covered[cmd] = new CoverageInfo(reason);
                    coverageEdges.Add(string.Format("{0} by {1}", checkId, reason));
                }
                state.Assume(assertCmd.Expr, checkId);
                return;
            }

            if (cmd is AssignCmd assignCmd)
            {
                state.Assign(assignCmd);
                return;
            }

            if (cmd is HavocCmd havocCmd)
            {
                state.Havoc(havocCmd.Vars.Select(v => v.Decl.Name));
                return;
            }

            if (cmd is CallCmd callCmd)
            {
                if (IsSmackOverflowCheck(callCmd))
                {
                    var checkId = GetCallCheckId(callCmd, procName, blockName, cmdIndex);
                    if (covered != null)
                    {
                        totalChecks++;
                    }
                    if (state.ImpliesSmackOverflowFlagIsZero(callCmd.Ins[0], out var reason) && covered != null)
                    {
                        coveredChecks++;
                        covered[cmd] = new CoverageInfo(reason);
                        coverageEdges.Add(string.Format("{0} by {1}", checkId, reason));
                    }
                    state.AssumeSmackOverflowFlagIsZero(callCmd.Ins[0], checkId);
                    return;
                }

                state.Havoc(GetModifiedVars(callCmd));
                return;
            }

            if (cmd is ParCallCmd parCallCmd)
            {
                var modified = new HashSet<string>();
                foreach (var call in parCallCmd.CallCmds)
                {
                    modified.UnionWith(GetModifiedVars(call));
                }
                state.Havoc(modified);
            }
        }

        private static HashSet<string> GetModifiedVars(CallCmd callCmd)
        {
            var ret = new HashSet<string>();
            foreach (var outParam in callCmd.Outs)
            {
                if (outParam != null)
                {
                    ret.Add(outParam.Decl != null ? outParam.Decl.Name : outParam.Name);
                }
            }

            if (callCmd.Proc != null)
            {
                foreach (var modified in callCmd.Proc.Modifies)
                {
                    ret.Add(modified.Decl != null ? modified.Decl.Name : modified.Name);
                }
            }

            return ret;
        }

        private void RewriteImplementation(Implementation impl, Dictionary<Cmd, CoverageInfo> covered)
        {
            foreach (var block in impl.Blocks)
            {
                var newCmds = new List<Cmd>();

                foreach (var cmd in block.Cmds)
                {
                    var rewritten = RewriteCmd(impl.Name, cmd, covered);
                    tinfo.add(impl.Name, block.Label, new InstrTrans(cmd, rewritten.Commands, rewritten.CorrespondingIndex));
                    newCmds.AddRange(rewritten.Commands);
                }

                block.Cmds = newCmds;
            }
        }

        private RewriteResult RewriteCmd(string procName, Cmd cmd, Dictionary<Cmd, CoverageInfo> covered)
        {
            if (cmd is AssertCmd assertCmd && IsSmackCheck(assertCmd) && procName != SmackOverflowProc)
            {
                var checkId = GetCheckId(assertCmd, procName, "", -1);
                if (covered.TryGetValue(cmd, out var info))
                {
                    var attrs = AddAttribute(assertCmd.Attributes, CoveredReasonAttr, info.Reason);
                    attrs = AddAttribute(attrs, CoveredByAttr, info.Reason);
                    attrs = AddAttribute(attrs, CoveredAttr);
                    var assume = new AssumeCmd(assertCmd.tok, DuplicateExpr(assertCmd.Expr), attrs);
                    return new RewriteResult(new List<Cmd> { assume }, 0);
                }
                else
                {
                    var learnedAttrs = AddAttribute(assertCmd.Attributes, LearnedFromAttr, checkId);
                    learnedAttrs = AddAttribute(learnedAttrs, LearnedAttr);
                    var assume = new AssumeCmd(assertCmd.tok, DuplicateExpr(assertCmd.Expr), learnedAttrs);
                    return new RewriteResult(new List<Cmd> { assertCmd, assume }, 0);
                }
            }

            if (cmd is CallCmd callCmd && IsSmackOverflowCheck(callCmd))
            {
                var checkId = GetCallCheckId(callCmd, procName, "", -1);
                if (covered.TryGetValue(cmd, out var info))
                {
                    var attrs = AddAttribute(callCmd.Attributes, CoveredReasonAttr, info.Reason);
                    attrs = AddAttribute(attrs, CoveredByAttr, info.Reason);
                    attrs = AddAttribute(attrs, CoveredAttr);
                    attrs = AddAttribute(attrs, CheckKindAttr, "overflow");
                    var assume = new AssumeCmd(callCmd.tok, SmackOverflowSafety(callCmd), attrs);
                    return new RewriteResult(new List<Cmd> { assume }, 0);
                }
                else
                {
                    var learnedAttrs = AddAttribute(callCmd.Attributes, LearnedFromAttr, checkId);
                    learnedAttrs = AddAttribute(learnedAttrs, LearnedAttr);
                    learnedAttrs = AddAttribute(learnedAttrs, CheckKindAttr, "overflow");
                    var assume = new AssumeCmd(callCmd.tok, SmackOverflowSafety(callCmd), learnedAttrs);
                    return new RewriteResult(new List<Cmd> { callCmd, assume }, 0);
                }
            }

            return new RewriteResult(new List<Cmd> { cmd }, 0);
        }

        private Expr DuplicateExpr(Expr expr)
        {
            return (Expr)duplicator.VisitExpr(expr);
        }

        private static IEnumerable<string> GetSuccessors(Block block)
        {
            var gotoCmd = block.TransferCmd as GotoCmd;
            if (gotoCmd == null)
            {
                return Enumerable.Empty<string>();
            }
            return gotoCmd.labelNames;
        }

        private static bool IsSmackCheck(AssertCmd cmd)
        {
            var attrs = cmd.Attributes;
            if (QKeyValue.FindStringAttribute(attrs, CheckIdAttr) != null ||
                QKeyValue.FindStringAttribute(attrs, CheckIdAttrCompat) != null ||
                QKeyValue.FindStringAttribute(attrs, CheckKindAttr) != null ||
                QKeyValue.FindStringAttribute(attrs, CheckKindAttrCompat) != null)
            {
                return true;
            }

            return BoogieUtil.checkAttrExists("overflow", attrs) ||
                   BoogieUtil.checkAttrExists("bounds", attrs) ||
                   BoogieUtil.checkAttrExists("division", attrs) ||
                   BoogieUtil.checkAttrExists("memory", attrs) ||
                   BoogieUtil.checkAttrExists("shift", attrs);
        }

        private static bool IsSmackOverflowCheck(CallCmd callCmd)
        {
            return callCmd.callee == SmackOverflowProc && callCmd.Ins.Count == 1;
        }

        private static Expr SmackOverflowSafety(CallCmd callCmd)
        {
            return Expr.Eq(callCmd.Ins[0], ZeroLike(callCmd.Ins[0]));
        }

        internal static Expr ZeroLike(Expr expr)
        {
            var type = ExprType(expr);
            if (type != null && type.IsBv)
            {
                return new LiteralExpr(Token.NoToken, BigNum.FromInt(0), type.BvBits, true);
            }

            return Expr.Literal(0);
        }

        internal static Microsoft.Boogie.Type ExprType(Expr expr)
        {
            if (expr.Type != null)
            {
                return expr.Type;
            }

            if (expr is IdentifierExpr identifierExpr && identifierExpr.Decl != null)
            {
                return identifierExpr.Decl.TypedIdent.Type;
            }

            return null;
        }

        private static string GetCallCheckId(CallCmd callCmd, string procName, string blockName, int cmdIndex)
        {
            var id = QKeyValue.FindStringAttribute(callCmd.Attributes, CheckIdAttr);
            if (id == null)
            {
                id = QKeyValue.FindStringAttribute(callCmd.Attributes, CheckIdAttrCompat);
            }
            if (id != null)
            {
                return id;
            }

            if (blockName == "")
            {
                return string.Format("overflow:{0}:{1}", procName, SmackOverflowProc);
            }
            return string.Format("overflow:{0}:{1}:{2}", procName, blockName, cmdIndex);
        }

        private static string GetCheckId(AssertCmd cmd, string procName, string blockName, int cmdIndex)
        {
            var ret = QKeyValue.FindStringAttribute(cmd.Attributes, CheckIdAttr);
            if (ret == null)
            {
                ret = QKeyValue.FindStringAttribute(cmd.Attributes, CheckIdAttrCompat);
            }
            if (ret != null)
            {
                return ret;
            }

            var kind = QKeyValue.FindStringAttribute(cmd.Attributes, CheckKindAttr) ??
                       QKeyValue.FindStringAttribute(cmd.Attributes, CheckKindAttrCompat) ??
                       "check";
            if (blockName == "")
            {
                return string.Format("{0}:{1}", kind, procName);
            }
            return string.Format("{0}:{1}:{2}:{3}", kind, procName, blockName, cmdIndex);
        }

        private static QKeyValue AddAttribute(QKeyValue attrs, string key)
        {
            return new QKeyValue(Token.NoToken, key, new List<object>(), attrs);
        }

        private static QKeyValue AddAttribute(QKeyValue attrs, string key, string value)
        {
            return new QKeyValue(Token.NoToken, key, new List<object> { value }, attrs);
        }

        private class CoverageInfo
        {
            public readonly string Reason;

            public CoverageInfo(string reason)
            {
                Reason = reason;
            }
        }

        private class RewriteResult
        {
            public readonly List<Cmd> Commands;
            public readonly int CorrespondingIndex;

            public RewriteResult(List<Cmd> commands, int correspondingIndex)
            {
                Commands = commands;
                CorrespondingIndex = correspondingIndex;
            }
        }
    }

    internal class AbstractState
    {
        private static readonly BigNum Zero = BigNum.FromInt(0);
        private static readonly BigNum One = BigNum.FromInt(1);

        private readonly Dictionary<string, FactSource> facts;
        private readonly Dictionary<LinearExpr, Bound> upperBounds;
        private readonly Dictionary<string, LinearExpr> env;
        private readonly Dictionary<string, Expr> exprEnv;

        public bool IsBottom { get; private set; }

        private AbstractState()
        {
            facts = new Dictionary<string, FactSource>();
            upperBounds = new Dictionary<LinearExpr, Bound>();
            env = new Dictionary<string, LinearExpr>();
            exprEnv = new Dictionary<string, Expr>();
        }

        public static AbstractState Top()
        {
            return new AbstractState();
        }

        public AbstractState Clone()
        {
            var ret = new AbstractState();
            ret.IsBottom = IsBottom;
            foreach (var kv in facts)
            {
                ret.facts.Add(kv.Key, kv.Value);
            }
            foreach (var kv in upperBounds)
            {
                ret.upperBounds.Add(kv.Key, kv.Value);
            }
            foreach (var kv in env)
            {
                ret.env.Add(kv.Key, kv.Value);
            }
            foreach (var kv in exprEnv)
            {
                ret.exprEnv.Add(kv.Key, kv.Value);
            }
            return ret;
        }

        public static bool Same(AbstractState a, AbstractState b)
        {
            if (a == null || b == null)
            {
                return a == null && b == null;
            }
            return a.Equals(b);
        }

        public static AbstractState Join(AbstractState a, AbstractState b)
        {
            if (a == null)
            {
                return b == null ? null : b.Clone();
            }
            if (b == null)
            {
                return a.Clone();
            }
            if (a.IsBottom)
            {
                return b.Clone();
            }
            if (b.IsBottom)
            {
                return a.Clone();
            }

            var ret = new AbstractState();

            foreach (var kv in a.facts)
            {
                if (b.facts.TryGetValue(kv.Key, out var src))
                {
                    ret.facts.Add(kv.Key, kv.Value.Merge(src));
                }
            }

            foreach (var kv in a.upperBounds)
            {
                if (b.upperBounds.TryGetValue(kv.Key, out var bound))
                {
                    ret.upperBounds.Add(kv.Key, Bound.Join(kv.Value, bound));
                }
            }

            foreach (var kv in a.env)
            {
                if (b.env.TryGetValue(kv.Key, out var value) && kv.Value.Equals(value))
                {
                    ret.env.Add(kv.Key, kv.Value);
                }
            }

            foreach (var kv in a.exprEnv)
            {
                if (b.exprEnv.TryGetValue(kv.Key, out var value) && ExprEqual(kv.Value, value))
                {
                    ret.exprEnv.Add(kv.Key, kv.Value);
                }
            }

            return ret;
        }

        public void Assume(Expr expr, string source)
        {
            if (IsBottom)
            {
                return;
            }

            if (IsTrue(expr))
            {
                return;
            }
            if (IsFalse(expr))
            {
                IsBottom = true;
                return;
            }

            if (TryGetBinary(expr, BinaryOperator.Opcode.And, out var lhs, out var rhs))
            {
                Assume(lhs, source);
                Assume(rhs, source);
                return;
            }

            if (TryDecodeSmackBooleanAssumption(expr, out var decodedBounds))
            {
                foreach (var decodedBound in decodedBounds)
                {
                    AddBound(decodedBound.Key, decodedBound.Value, source);
                }
            }

            AddFact(expr, source);
        }

        public bool Implies(Expr expr, out string reason)
        {
            reason = "unreachable";
            if (IsBottom)
            {
                return true;
            }

            if (IsTrue(expr))
            {
                reason = "true";
                return true;
            }

            if (TryGetBinary(expr, BinaryOperator.Opcode.And, out var lhs, out var rhs))
            {
                if (Implies(lhs, out var lhsReason) && Implies(rhs, out var rhsReason))
                {
                    reason = CombineReason(lhsReason, rhsReason);
                    return true;
                }
                return false;
            }

            if (TryGetBinary(expr, BinaryOperator.Opcode.Or, out lhs, out rhs))
            {
                if (Implies(lhs, out reason) || Implies(rhs, out reason))
                {
                    return true;
                }
                return false;
            }

            if (TryGetBinary(expr, BinaryOperator.Opcode.Eq, out lhs, out rhs))
            {
                if (TryGetLinearInequality(lhs, rhs, false, out var key1, out var bound1) &&
                    TryGetLinearInequality(rhs, lhs, false, out var key2, out var bound2) &&
                    ImpliesBound(key1, bound1, out var reason1) &&
                    ImpliesBound(key2, bound2, out var reason2))
                {
                    reason = CombineReason(reason1, reason2);
                    return true;
                }
            }

            if (TryGetComparisonBound(expr, out var key, out var bound) &&
                ImpliesBound(key, bound, out reason))
            {
                return true;
            }

            var fact = CanonicalFact(expr);
            if (facts.TryGetValue(fact, out var src))
            {
                reason = src.Source;
                return true;
            }

            return false;
        }

        public void AssumeSmackOverflowFlagIsZero(Expr flag, string source)
        {
            if (TryDecodeSmackOverflowFlagZero(flag, out var bounds))
            {
                foreach (var bound in bounds)
                {
                    AddBound(bound.Key, bound.Value, source);
                }

                AddFact(Expr.Eq(flag, SmackDependencyAnalysis.ZeroLike(flag)), source);
                return;
            }

            Assume(Expr.Eq(flag, SmackDependencyAnalysis.ZeroLike(flag)), source);
        }

        public bool ImpliesSmackOverflowFlagIsZero(Expr flag, out string reason)
        {
            if (TryDecodeSmackOverflowFlagZero(flag, out var bounds))
            {
                reason = null;
                foreach (var bound in bounds)
                {
                    if (!ImpliesBound(bound.Key, bound.Value, out var boundReason))
                    {
                        reason = null;
                        return false;
                    }

                    reason = reason == null ? boundReason : CombineReason(reason, boundReason);
                }

                if (reason == null)
                {
                    reason = "decoded overflow flag";
                }
                return true;
            }

            return Implies(Expr.Eq(flag, SmackDependencyAnalysis.ZeroLike(flag)), out reason);
        }

        public void Assign(AssignCmd cmd)
        {
            var assigned = new HashSet<string>(cmd.Lhss.Select(lhs => lhs.DeepAssignedVariable.Name));
            var rhsValues = new Dictionary<string, LinearExpr>();
            var rhsExprs = new Dictionary<string, Expr>();

            for (int i = 0; i < cmd.Lhss.Count; i++)
            {
                var lhs = cmd.Lhss[i].DeepAssignedVariable.Name;
                if (!(cmd.Lhss[i] is SimpleAssignLhs) || ExprUsesAny(cmd.Rhss[i], assigned))
                {
                    continue;
                }

                rhsExprs[lhs] = cmd.Rhss[i];
                if (TryLinearize(cmd.Rhss[i], out var value) && !value.UsesAny(assigned))
                {
                    rhsValues[lhs] = value;
                }
            }

            Havoc(assigned);

            foreach (var kv in rhsValues)
            {
                env[kv.Key] = kv.Value;
            }
            foreach (var kv in rhsExprs)
            {
                exprEnv[kv.Key] = kv.Value;
            }
        }

        public void Havoc(IEnumerable<string> vars)
        {
            var killed = new HashSet<string>(vars);
            if (killed.Count == 0)
            {
                return;
            }

            foreach (var name in killed)
            {
                env.Remove(name);
                exprEnv.Remove(name);
            }

            foreach (var name in env.Where(kv => kv.Value.UsesAny(killed)).Select(kv => kv.Key).ToList())
            {
                env.Remove(name);
            }

            foreach (var name in exprEnv.Where(kv => ExprUsesAny(kv.Value, killed)).Select(kv => kv.Key).ToList())
            {
                exprEnv.Remove(name);
            }

            foreach (var key in facts.Keys.Where(k => FactUsesAny(k, killed)).ToList())
            {
                facts.Remove(key);
            }

            foreach (var key in upperBounds.Keys.Where(k => k.UsesAny(killed)).ToList())
            {
                upperBounds.Remove(key);
            }
        }

        private void AddFact(Expr expr, string source)
        {
            if (TryGetComparisonBound(expr, out var key, out var bound))
            {
                AddBound(key, bound, source);
                return;
            }

            if (TryGetBinary(expr, BinaryOperator.Opcode.Eq, out var lhs, out var rhs) &&
                TryGetLinearInequality(lhs, rhs, false, out var key1, out var bound1) &&
                TryGetLinearInequality(rhs, lhs, false, out var key2, out var bound2))
            {
                AddBound(key1, bound1, source);
                AddBound(key2, bound2, source);
            }

            var fact = CanonicalFact(expr);
            facts[fact] = new FactSource(source);
        }

        private void AddBound(LinearExpr key, BigNum value, string source)
        {
            if (!upperBounds.TryGetValue(key, out var old) || value < old.Value)
            {
                upperBounds[key] = new Bound(value, source);
            }
        }

        private bool ImpliesBound(LinearExpr key, BigNum value, out string reason)
        {
            if (upperBounds.TryGetValue(key, out var old) && old.Value <= value)
            {
                reason = old.Source;
                return true;
            }

            reason = null;
            return false;
        }

        private bool TryDecodeSmackOverflowFlagZero(Expr flag, out List<DecodedBound> bounds)
        {
            bounds = new List<DecodedBound>();
            return TryDecodeSmackOverflowFlagZero(flag, bounds, new HashSet<string>());
        }

        private bool TryDecodeSmackOverflowFlagZero(
            Expr flag,
            List<DecodedBound> bounds,
            HashSet<string> seen)
        {
            if (IsBitVectorExpr(flag))
            {
                return false;
            }

            if (flag is LiteralExpr literalExpr)
            {
                return literalExpr.Val is BigNum num && num == Zero;
            }

            if (flag is IdentifierExpr identifierExpr && identifierExpr.Decl != null &&
                exprEnv.TryGetValue(identifierExpr.Decl.Name, out var definition))
            {
                if (!seen.Add(identifierExpr.Decl.Name))
                {
                    return false;
                }

                var ret = TryDecodeSmackOverflowFlagZero(definition, bounds, seen);
                seen.Remove(identifierExpr.Decl.Name);
                return ret;
            }

            if (!TryGetFunctionCall(flag, out var functionName, out var args))
            {
                return false;
            }

            if (IsSmackFlagCast(functionName) && args.Count == 1)
            {
                return TryDecodeSmackOverflowFlagZero(args[0], bounds, seen);
            }

            if (functionName.StartsWith("$or.", StringComparison.Ordinal) && args.Count == 2)
            {
                var leftBounds = new List<DecodedBound>();
                var rightBounds = new List<DecodedBound>();
                if (!TryDecodeSmackOverflowFlagZero(args[0], leftBounds, seen) ||
                    !TryDecodeSmackOverflowFlagZero(args[1], rightBounds, seen))
                {
                    return false;
                }

                bounds.AddRange(leftBounds);
                bounds.AddRange(rightBounds);
                return true;
            }

            if (functionName.StartsWith("$sgt.", StringComparison.Ordinal) && args.Count == 2)
            {
                return AddDecodedBound(args[0], args[1], false, bounds);
            }

            if (functionName.StartsWith("$slt.", StringComparison.Ordinal) && args.Count == 2)
            {
                return AddDecodedBound(args[1], args[0], false, bounds);
            }

            return false;
        }

        private bool AddDecodedBound(Expr lhs, Expr rhs, bool strict, List<DecodedBound> bounds)
        {
            if (!TryGetLinearInequality(lhs, rhs, strict, out var key, out var bound))
            {
                return false;
            }

            bounds.Add(new DecodedBound(key, bound));
            return true;
        }

        private bool TryDecodeSmackBooleanAssumption(Expr expr, out List<DecodedBound> bounds)
        {
            bounds = new List<DecodedBound>();
            if (IsBitVectorExpr(expr))
            {
                return false;
            }

            if (TryGetNot(expr, out var inner))
            {
                return TryDecodeSmackBooleanAssumption(inner, false, bounds);
            }

            return TryDecodeSmackBooleanAssumption(expr, true, bounds);
        }

        private bool TryDecodeSmackBooleanAssumption(Expr expr, bool truth, List<DecodedBound> bounds)
        {
            if (TryGetBinary(expr, BinaryOperator.Opcode.Eq, out var lhs, out var rhs))
            {
                if (TryGetIntegerLiteral(rhs, out var rhsValue))
                {
                    if (rhsValue == One)
                    {
                        return TryDecodeSmackBoolean(lhs, truth, bounds, new HashSet<string>());
                    }
                    if (rhsValue == Zero)
                    {
                        return TryDecodeSmackBoolean(lhs, !truth, bounds, new HashSet<string>());
                    }
                }

                if (TryGetIntegerLiteral(lhs, out var lhsValue))
                {
                    if (lhsValue == One)
                    {
                        return TryDecodeSmackBoolean(rhs, truth, bounds, new HashSet<string>());
                    }
                    if (lhsValue == Zero)
                    {
                        return TryDecodeSmackBoolean(rhs, !truth, bounds, new HashSet<string>());
                    }
                }
            }

            return truth && TryDecodeSmackBoolean(expr, true, bounds, new HashSet<string>());
        }

        private bool TryDecodeSmackBoolean(
            Expr flag,
            bool truth,
            List<DecodedBound> bounds,
            HashSet<string> seen)
        {
            if (flag is LiteralExpr literalExpr)
            {
                return literalExpr.Val is BigNum num && ((num != Zero) == truth);
            }

            if (flag is IdentifierExpr identifierExpr && identifierExpr.Decl != null &&
                exprEnv.TryGetValue(identifierExpr.Decl.Name, out var definition))
            {
                if (!seen.Add(identifierExpr.Decl.Name))
                {
                    return false;
                }

                var ret = TryDecodeSmackBoolean(definition, truth, bounds, seen);
                seen.Remove(identifierExpr.Decl.Name);
                return ret;
            }

            if (TryGetNot(flag, out var inner))
            {
                return TryDecodeSmackBoolean(inner, !truth, bounds, seen);
            }

            if (!TryGetFunctionCall(flag, out var functionName, out var args))
            {
                return false;
            }

            if (IsSmackFlagCast(functionName) && args.Count == 1)
            {
                return TryDecodeSmackBoolean(args[0], truth, bounds, seen);
            }

            if (functionName.StartsWith("$xor.", StringComparison.Ordinal) && args.Count == 2)
            {
                if (TryGetIntegerLiteral(args[0], out var leftValue))
                {
                    if (leftValue == One)
                    {
                        return TryDecodeSmackBoolean(args[1], !truth, bounds, seen);
                    }
                    if (leftValue == Zero)
                    {
                        return TryDecodeSmackBoolean(args[1], truth, bounds, seen);
                    }
                }
                if (TryGetIntegerLiteral(args[1], out var rightValue))
                {
                    if (rightValue == One)
                    {
                        return TryDecodeSmackBoolean(args[0], !truth, bounds, seen);
                    }
                    if (rightValue == Zero)
                    {
                        return TryDecodeSmackBoolean(args[0], truth, bounds, seen);
                    }
                }
                return false;
            }

            if (functionName.StartsWith("$or.", StringComparison.Ordinal) && args.Count == 2 && !truth)
            {
                var leftBounds = new List<DecodedBound>();
                var rightBounds = new List<DecodedBound>();
                if (!TryDecodeSmackBoolean(args[0], false, leftBounds, seen) ||
                    !TryDecodeSmackBoolean(args[1], false, rightBounds, seen))
                {
                    return false;
                }

                bounds.AddRange(leftBounds);
                bounds.AddRange(rightBounds);
                return true;
            }

            if (functionName.StartsWith("$and.", StringComparison.Ordinal) && args.Count == 2 && truth)
            {
                var leftBounds = new List<DecodedBound>();
                var rightBounds = new List<DecodedBound>();
                if (!TryDecodeSmackBoolean(args[0], true, leftBounds, seen) ||
                    !TryDecodeSmackBoolean(args[1], true, rightBounds, seen))
                {
                    return false;
                }

                bounds.AddRange(leftBounds);
                bounds.AddRange(rightBounds);
                return true;
            }

            if (args.Count != 2)
            {
                return false;
            }

            if (functionName.StartsWith("$sgt.", StringComparison.Ordinal))
            {
                return truth
                    ? AddDecodedBound(args[1], args[0], true, bounds)
                    : AddDecodedBound(args[0], args[1], false, bounds);
            }

            if (functionName.StartsWith("$slt.", StringComparison.Ordinal))
            {
                return truth
                    ? AddDecodedBound(args[0], args[1], true, bounds)
                    : AddDecodedBound(args[1], args[0], false, bounds);
            }

            if (functionName.StartsWith("$sge.", StringComparison.Ordinal))
            {
                return truth
                    ? AddDecodedBound(args[1], args[0], false, bounds)
                    : AddDecodedBound(args[0], args[1], true, bounds);
            }

            if (functionName.StartsWith("$sle.", StringComparison.Ordinal))
            {
                return truth
                    ? AddDecodedBound(args[0], args[1], false, bounds)
                    : AddDecodedBound(args[1], args[0], true, bounds);
            }

            return false;
        }

        private bool TryGetComparisonBound(Expr expr, out LinearExpr key, out BigNum bound)
        {
            if (TryGetBinary(expr, BinaryOperator.Opcode.Le, out var lhs, out var rhs))
            {
                return TryGetLinearInequality(lhs, rhs, false, out key, out bound);
            }
            if (TryGetBinary(expr, BinaryOperator.Opcode.Lt, out lhs, out rhs))
            {
                return TryGetLinearInequality(lhs, rhs, true, out key, out bound);
            }
            if (TryGetBinary(expr, BinaryOperator.Opcode.Ge, out lhs, out rhs))
            {
                return TryGetLinearInequality(rhs, lhs, false, out key, out bound);
            }
            if (TryGetBinary(expr, BinaryOperator.Opcode.Gt, out lhs, out rhs))
            {
                return TryGetLinearInequality(rhs, lhs, true, out key, out bound);
            }

            key = null;
            bound = Zero;
            return false;
        }

        private bool TryGetLinearInequality(
            Expr lhs, Expr rhs, bool strict, out LinearExpr key, out BigNum bound)
        {
            key = null;
            bound = Zero;
            if (!TryLinearize(lhs, out var lhsLinear) || !TryLinearize(rhs, out var rhsLinear))
            {
                return false;
            }

            var diff = lhsLinear.Sub(rhsLinear);
            key = diff.WithoutConstant();
            bound = -diff.Constant;
            if (strict)
            {
                bound -= One;
            }
            return true;
        }

        private bool TryLinearize(Expr expr, out LinearExpr result)
        {
            result = null;

            if (IsBitVectorExpr(expr))
            {
                return false;
            }

            if (expr is IdentifierExpr identifierExpr)
            {
                if (identifierExpr.Decl == null)
                {
                    return false;
                }

                if (env.TryGetValue(identifierExpr.Decl.Name, out var value))
                {
                    result = value;
                    return true;
                }

                result = LinearExpr.Variable(identifierExpr.Decl.Name);
                return true;
            }

            if (expr is LiteralExpr literalExpr)
            {
                if (literalExpr.Val is BigNum num)
                {
                    result = LinearExpr.ConstantExpr(num);
                    return true;
                }
                return false;
            }

            if (!(expr is NAryExpr naryExpr))
            {
                return false;
            }

            if (naryExpr.Fun is UnaryOperator unary)
            {
                if (unary.Op == UnaryOperator.Opcode.Neg &&
                    TryLinearize(naryExpr.Args[0], out var inner))
                {
                    result = inner.Scale(BigNum.FromInt(-1));
                    return true;
                }
                return false;
            }

            if (naryExpr.Fun is FunctionCall functionCall)
            {
                return TryLinearizeFunctionCall(functionCall.FunctionName, naryExpr.Args, out result);
            }

            if (!(naryExpr.Fun is BinaryOperator binary) || naryExpr.Args.Count != 2)
            {
                return false;
            }

            var leftExpr = naryExpr.Args[0];
            var rightExpr = naryExpr.Args[1];
            switch (binary.Op)
            {
                case BinaryOperator.Opcode.Add:
                    if (TryLinearize(leftExpr, out var addLeft) && TryLinearize(rightExpr, out var addRight))
                    {
                        result = addLeft.Add(addRight);
                        return true;
                    }
                    return false;

                case BinaryOperator.Opcode.Sub:
                    if (TryLinearize(leftExpr, out var subLeft) && TryLinearize(rightExpr, out var subRight))
                    {
                        result = subLeft.Sub(subRight);
                        return true;
                    }
                    return false;

                case BinaryOperator.Opcode.Mul:
                    if (TryLinearize(leftExpr, out var mulLeft) && mulLeft.IsConstant &&
                        TryLinearize(rightExpr, out var mulRight))
                    {
                        result = mulRight.Scale(mulLeft.Constant);
                        return true;
                    }
                    if (TryLinearize(rightExpr, out mulRight) && mulRight.IsConstant &&
                        TryLinearize(leftExpr, out mulLeft))
                    {
                        result = mulLeft.Scale(mulRight.Constant);
                        return true;
                    }
                    return false;

                default:
                    return false;
            }
        }

        private bool TryLinearizeFunctionCall(string functionName, IList<Expr> args, out LinearExpr result)
        {
            result = null;
            if (functionName == null)
            {
                return false;
            }

            if (IsLinearIdentityCast(functionName) && args.Count == 1)
            {
                return TryLinearize(args[0], out result);
            }

            if (args.Count != 2)
            {
                return false;
            }

            if (functionName.StartsWith("$add.", StringComparison.Ordinal))
            {
                if (TryLinearize(args[0], out var addLeft) && TryLinearize(args[1], out var addRight))
                {
                    result = addLeft.Add(addRight);
                    return true;
                }
                return false;
            }

            if (functionName.StartsWith("$sub.", StringComparison.Ordinal))
            {
                if (TryLinearize(args[0], out var subLeft) && TryLinearize(args[1], out var subRight))
                {
                    result = subLeft.Sub(subRight);
                    return true;
                }
                return false;
            }

            if (functionName.StartsWith("$mul.", StringComparison.Ordinal))
            {
                if (TryLinearize(args[0], out var mulLeft) && mulLeft.IsConstant &&
                    TryLinearize(args[1], out var mulRight))
                {
                    result = mulRight.Scale(mulLeft.Constant);
                    return true;
                }
                if (TryLinearize(args[1], out mulRight) && mulRight.IsConstant &&
                    TryLinearize(args[0], out mulLeft))
                {
                    result = mulLeft.Scale(mulRight.Constant);
                    return true;
                }
            }

            return false;
        }

        private string CanonicalFact(Expr expr)
        {
            if (TryGetComparisonBound(expr, out var key, out var bound))
            {
                return string.Format("{0} <= {1}", key, bound);
            }
            return expr.ToString();
        }

        private static bool TryGetBinary(Expr expr, BinaryOperator.Opcode op, out Expr lhs, out Expr rhs)
        {
            lhs = null;
            rhs = null;
            if (!(expr is NAryExpr naryExpr) || !(naryExpr.Fun is BinaryOperator binary) ||
                naryExpr.Args.Count != 2 || binary.Op != op)
            {
                return false;
            }

            lhs = naryExpr.Args[0];
            rhs = naryExpr.Args[1];
            return true;
        }

        private static bool TryGetNot(Expr expr, out Expr inner)
        {
            inner = null;
            if (!(expr is NAryExpr naryExpr) || !(naryExpr.Fun is UnaryOperator unary) ||
                unary.Op != UnaryOperator.Opcode.Not || naryExpr.Args.Count != 1)
            {
                return false;
            }

            inner = naryExpr.Args[0];
            return true;
        }

        private static bool TryGetIntegerLiteral(Expr expr, out BigNum value)
        {
            value = Zero;
            if (expr is LiteralExpr literalExpr && literalExpr.Val is BigNum num)
            {
                value = num;
                return true;
            }

            return false;
        }

        private static bool TryGetFunctionCall(Expr expr, out string functionName, out IList<Expr> args)
        {
            functionName = null;
            args = null;
            if (!(expr is NAryExpr naryExpr) || !(naryExpr.Fun is FunctionCall functionCall))
            {
                return false;
            }

            functionName = functionCall.FunctionName;
            args = naryExpr.Args;
            return functionName != null;
        }

        private static bool IsSmackFlagCast(string functionName)
        {
            return functionName.StartsWith("$zext.", StringComparison.Ordinal) ||
                   functionName.StartsWith("$sext.", StringComparison.Ordinal) ||
                   functionName.StartsWith("$trunc.", StringComparison.Ordinal);
        }

        private static bool IsLinearIdentityCast(string functionName)
        {
            return functionName.StartsWith("$sext.", StringComparison.Ordinal);
        }

        private static bool ExprUsesAny(Expr expr, HashSet<string> vars)
        {
            return VarsUsed.GetVarsUsed(expr).Any(vars.Contains);
        }

        private static bool ExprEqual(Expr lhs, Expr rhs)
        {
            return lhs.ToString() == rhs.ToString();
        }

        private static bool IsBitVectorExpr(Expr expr)
        {
            var type = SmackDependencyAnalysis.ExprType(expr);
            return type != null && type.IsBv;
        }

        private static bool IsTrue(Expr expr)
        {
            return expr is LiteralExpr lit && lit.IsTrue;
        }

        private static bool IsFalse(Expr expr)
        {
            return expr is LiteralExpr lit && lit.IsFalse;
        }

        private static bool FactUsesAny(string fact, HashSet<string> vars)
        {
            return vars.Any(v => fact.Contains(v));
        }

        private static string CombineReason(string lhs, string rhs)
        {
            return MergeSources(lhs, rhs, ",");
        }

        private static string MergeSources(string lhs, string rhs, string separator)
        {
            if (lhs == rhs)
            {
                return lhs;
            }

            var values = new SortedSet<string>();
            foreach (var value in lhs.Split(new[] { "|", "," }, StringSplitOptions.RemoveEmptyEntries))
            {
                values.Add(value);
            }
            foreach (var value in rhs.Split(new[] { "|", "," }, StringSplitOptions.RemoveEmptyEntries))
            {
                values.Add(value);
            }
            return string.Join(separator, values);
        }

        public override bool Equals(object obj)
        {
            if (!(obj is AbstractState other))
            {
                return false;
            }

            return IsBottom == other.IsBottom &&
                   DictionaryEqual(facts, other.facts) &&
                   DictionaryEqual(upperBounds, other.upperBounds) &&
                   DictionaryEqual(env, other.env) &&
                   ExprDictionaryEqual(exprEnv, other.exprEnv);
        }

        public override int GetHashCode()
        {
            var hash = IsBottom ? 17 : 23;
            hash = HashDictionary(hash, facts);
            hash = HashDictionary(hash, upperBounds);
            hash = HashDictionary(hash, env);
            hash = HashExprDictionary(hash, exprEnv);
            return hash;
        }

        private static bool DictionaryEqual<TKey, TValue>(
            Dictionary<TKey, TValue> lhs, Dictionary<TKey, TValue> rhs)
        {
            if (lhs.Count != rhs.Count)
            {
                return false;
            }
            foreach (var kv in lhs)
            {
                if (!rhs.TryGetValue(kv.Key, out var value) || !Equals(kv.Value, value))
                {
                    return false;
                }
            }
            return true;
        }

        private static bool ExprDictionaryEqual(Dictionary<string, Expr> lhs, Dictionary<string, Expr> rhs)
        {
            if (lhs.Count != rhs.Count)
            {
                return false;
            }
            foreach (var kv in lhs)
            {
                if (!rhs.TryGetValue(kv.Key, out var value) || !ExprEqual(kv.Value, value))
                {
                    return false;
                }
            }
            return true;
        }

        private static int HashDictionary<TKey, TValue>(int seed, Dictionary<TKey, TValue> dictionary)
        {
            var hash = seed;
            foreach (var kv in dictionary.OrderBy(kv => kv.Key.ToString()))
            {
                hash = hash * 31 + kv.Key.GetHashCode();
                hash = hash * 31 + kv.Value.GetHashCode();
            }
            return hash;
        }

        private static int HashExprDictionary(int seed, Dictionary<string, Expr> dictionary)
        {
            var hash = seed;
            foreach (var kv in dictionary.OrderBy(kv => kv.Key))
            {
                hash = hash * 31 + kv.Key.GetHashCode();
                hash = hash * 31 + kv.Value.ToString().GetHashCode();
            }
            return hash;
        }

        private class DecodedBound
        {
            public readonly LinearExpr Key;
            public readonly BigNum Value;

            public DecodedBound(LinearExpr key, BigNum value)
            {
                Key = key;
                Value = value;
            }
        }

        private class FactSource
        {
            public readonly string Source;

            public FactSource(string source)
            {
                Source = source;
            }

            public FactSource Merge(FactSource other)
            {
                return Source == other.Source ? this : new FactSource(MergeSources(Source, other.Source, "|"));
            }

            public override bool Equals(object obj)
            {
                return obj is FactSource other && Source == other.Source;
            }

            public override int GetHashCode()
            {
                return Source.GetHashCode();
            }
        }

        private class Bound
        {
            public readonly BigNum Value;
            public readonly string Source;

            public Bound(BigNum value, string source)
            {
                Value = value;
                Source = source;
            }

            public static Bound Join(Bound lhs, Bound rhs)
            {
                if (lhs.Value >= rhs.Value)
                {
                    return new Bound(lhs.Value, MergeSources(lhs.Source, rhs.Source, "|"));
                }
                return new Bound(rhs.Value, MergeSources(lhs.Source, rhs.Source, "|"));
            }

            public override bool Equals(object obj)
            {
                return obj is Bound other && Value == other.Value && Source == other.Source;
            }

            public override int GetHashCode()
            {
                return Value.GetHashCode() * 31 + Source.GetHashCode();
            }
        }
    }

    internal class LinearExpr
    {
        private static readonly BigNum Zero = BigNum.FromInt(0);
        private static readonly BigNum One = BigNum.FromInt(1);

        private readonly SortedDictionary<string, BigNum> terms;
        public BigNum Constant { get; private set; }

        public bool IsConstant
        {
            get { return terms.Count == 0; }
        }

        private LinearExpr(SortedDictionary<string, BigNum> terms, BigNum constant)
        {
            this.terms = terms;
            Constant = constant;
            Normalize();
        }

        public static LinearExpr Variable(string name)
        {
            return new LinearExpr(new SortedDictionary<string, BigNum> { { name, One } }, Zero);
        }

        public static LinearExpr ConstantExpr(BigNum value)
        {
            return new LinearExpr(new SortedDictionary<string, BigNum>(), value);
        }

        public LinearExpr Add(LinearExpr other)
        {
            var ret = CloneTerms();
            foreach (var kv in other.terms)
            {
                ret[kv.Key] = ret.ContainsKey(kv.Key) ? ret[kv.Key] + kv.Value : kv.Value;
            }
            return new LinearExpr(ret, Constant + other.Constant);
        }

        public LinearExpr Sub(LinearExpr other)
        {
            return Add(other.Scale(BigNum.FromInt(-1)));
        }

        public LinearExpr Scale(BigNum factor)
        {
            var ret = new SortedDictionary<string, BigNum>();
            foreach (var kv in terms)
            {
                ret[kv.Key] = kv.Value * factor;
            }
            return new LinearExpr(ret, Constant * factor);
        }

        public LinearExpr WithoutConstant()
        {
            return new LinearExpr(CloneTerms(), Zero);
        }

        public bool UsesAny(HashSet<string> vars)
        {
            return terms.Keys.Any(vars.Contains);
        }

        private SortedDictionary<string, BigNum> CloneTerms()
        {
            return new SortedDictionary<string, BigNum>(terms);
        }

        private void Normalize()
        {
            foreach (var key in terms.Where(kv => kv.Value == Zero).Select(kv => kv.Key).ToList())
            {
                terms.Remove(key);
            }
        }

        public override bool Equals(object obj)
        {
            if (!(obj is LinearExpr other) || Constant != other.Constant || terms.Count != other.terms.Count)
            {
                return false;
            }

            foreach (var kv in terms)
            {
                if (!other.terms.TryGetValue(kv.Key, out var value) || value != kv.Value)
                {
                    return false;
                }
            }
            return true;
        }

        public override int GetHashCode()
        {
            var hash = Constant.GetHashCode();
            foreach (var kv in terms)
            {
                hash = hash * 31 + kv.Key.GetHashCode();
                hash = hash * 31 + kv.Value.GetHashCode();
            }
            return hash;
        }

        public override string ToString()
        {
            var parts = new List<string>();
            foreach (var kv in terms)
            {
                if (kv.Value == One)
                {
                    parts.Add(kv.Key);
                }
                else
                {
                    parts.Add(kv.Value + "*" + kv.Key);
                }
            }
            if (Constant != Zero || parts.Count == 0)
            {
                parts.Add(Constant.ToString());
            }
            return string.Join(" + ", parts);
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;
using System.IO;
using ProgTransformation;
using System.Runtime.Serialization;
using System.Diagnostics.Contracts;

namespace cba
{
    // Represents an interprocedural path through a program. It does not store
    // the control-transfer instructions (goto, return). Should add these once
    // there is some use for them.
    [Serializable]
    public class ErrorTrace
    {
        // The procedure
        public string procName { get; private set; }

        // The blocks
        public List<ErrorTraceBlock> Blocks { get; private set; }

        // A map from labels to blocks
        private Dictionary<string, ErrorTraceBlock> blockMap;

        // Does this trace return from this procedure
        public bool returns { get; private set; }

        // Does the trace end by raisingException?
        public bool raisesException { get; private set; }

        public ErrorTrace(string _procName)
        {
            procName = _procName;
            Blocks = new List<ErrorTraceBlock>();
            returns = false;
            raisesException = false;
            blockMap = null;
        }

        public ErrorTrace(string _procName, string _startingBlockName)
        {
            procName = _procName;
            Blocks = new List<ErrorTraceBlock>();
            returns = false;
            raisesException = false;
            blockMap = null;
            Blocks.Add(new ErrorTraceBlock(_startingBlockName));
        }

        // A location identifier for an instruction
        public static string getInstructionLabel(string procName, string blockName, int instrNumber)
        {
            return procName + ":" + blockName + ":" + instrNumber.ToString();
        }

        public bool isIntra()
        {
            foreach (var blk in Blocks)
            {
                if (!blk.isIntra())
                    return false;
            }
            return true;
        }

        // Return the list of blocks in the trace (only in the current procedure)
        public List<string> getBlockLabels()
        {
            var ret = new List<string>();
            Blocks.Iter(blk => ret.Add(blk.blockName));
            return ret;
        }

        public ErrorTraceBlock getBlock(string blkName)
        {
            cacheBlockLabelMap();
            return blockMap[blkName];
        }

        private void cacheBlockLabelMap()
        {
            if (blockMap != null) return;
            blockMap = new Dictionary<string, ErrorTraceBlock>();
            Blocks.Iter(blk => blockMap.Add(blk.blockName, blk));
        }

        // Return the set of procedures that the trace passes through
        public HashSet<string> getProcs()
        {
            var ret = new HashSet<string>();
            ret.Add(procName);

            foreach (var blk in Blocks)
            {
                foreach (var cmd in blk.Cmds)
                {
                    if (cmd.CalleeTrace != null)
                    {
                        ret.UnionWith(cmd.CalleeTrace.getProcs());
                    }
                }
            }
            return ret;
        }

        // Add a block at the end of the trace
        public void addBlock(ErrorTraceBlock blk)
        {
            Debug.Assert(returns == false);

            // Where do we add succ?
            ErrorTrace currTrace = getCurrTrace();

            if (currTrace == null)
            {
                // It is an intra succ in the current procedure
                Blocks.Add(blk);
            }
            else
            {
                currTrace.addBlock(blk);
            }
        }

        // Add an (non-return) instruction at the end of the trace
        public void addInstr(ErrorTraceInstr instr)
        {
            Debug.Assert(returns == false);
            Debug.Assert(Blocks.Count != 0);

            // Where do we add instr?
            ErrorTrace currTrace = getCurrTrace();

            if (currTrace == null)
            {
                // It is an intra succ in the current procedure
                Blocks[Blocks.Count - 1].addInstr(instr);
            }
            else
            {
                currTrace.addInstr(instr);
            }
        }

        // Add a return at the end of the trace
        public void addReturn()
        {
            addReturn(false);
        }

        public void addReturn(bool withException)
        {
            Debug.Assert(returns == false);
            Debug.Assert(Blocks.Count != 0);

            // Where do we add succ?
            ErrorTrace currTrace = getCurrTrace();

            if (currTrace == null)
            {
                returns = true;
                raisesException = withException;
            }
            else
            {
                currTrace.addReturn(withException);
            }

        }

        // Trace ends by raising exception
        public void setRaiseException()
        {
            raisesException = true;
        }

        // Add a procedure call at the end of the trace
        public void addCall(string callee)
        {
            var et = new ErrorTrace(callee);
            var instr = new CallInstr(et);
            addInstr(instr);
        }

        public bool checkSanity()
        {
            var calleeAllReturn = true;
            for (int j = 0; j < Blocks.Count; j++)
            {
                var blk = Blocks[j];
                for (int i = 0; i < blk.Cmds.Count; i++)
                {
                    var cinst = blk.Cmds[i] as CallInstr;
                    if (cinst == null || cinst.calleeTrace == null) continue;
                    if (!cinst.calleeTrace.checkSanity())
                        return false;
                    if (!cinst.calleeTrace.returns && (i != blk.Cmds.Count - 1 || j != Blocks.Count - 1))
                        return false;
                    if (!cinst.calleeTrace.returns)
                        calleeAllReturn = false;
                }
            }
            if (returns && !calleeAllReturn)
                return false;

            return true;
        }

        public ErrorTrace findTrace(string callee)
        {
            if (procName == callee) return this;
            foreach (var blk in Blocks)
            {
                foreach (var inst in blk.Cmds.OfType<CallInstr>().Where(i => i.calleeTrace != null))
                {
                    if (inst.callee == callee)
                        return inst.calleeTrace;
                    var ret = inst.calleeTrace.findTrace(callee);
                    if (ret != null) return ret;
                }
            }
            return null;
        }

        public void printTrace(TokenTextWriter ttw)
        {
            if (ttw == null)
                return;

            printTrace(ttw, 0);
        }

        public void printTrace(TokenTextWriter ttw, int indent)
        {
            for (int i = 0; i < Blocks.Count; i++)
            {
                printIndent(ttw, indent); ttw.WriteLine(procName + ":" + Blocks[i].blockName);
                Blocks[i].printCalledTraces(ttw, procName, indent);
            }
        }

        public void printRecBound()
        {
            var stack = new Stack<string>();
            var bound = new Dictionary<string, int>();
            computeRecBound(this, stack, bound);
            foreach (var kvp in bound)
            {
                if (kvp.Value <= 1) continue;
                Console.WriteLine("RB for {0}: {1}", kvp.Key, kvp.Value);
            }
        }

        private static void computeRecBound(ErrorTrace trace, Stack<string> stack, Dictionary<string, int> bound)
        {
            if (trace == null) return;

            // compute bound for procName
            var rb = stack.Where(str => str == trace.procName).Count() + 1;
            if (!bound.ContainsKey(trace.procName))
            {
                bound.Add(trace.procName, 0);
            }
            var oldb = bound[trace.procName];
            if (rb > oldb) bound[trace.procName] = rb;

            stack.Push(trace.procName);
            foreach (var blk in trace.Blocks)
            {
                foreach (var cmd in blk.Cmds.OfType<CallInstr>())
                {
                    computeRecBound(cmd.calleeTrace, stack, bound);
                }
            }
            stack.Pop();
        }

        public ErrorTrace Copy()
        {
            var ret = new ErrorTrace(procName);

            foreach (var blk in Blocks)
            {
                ret.addBlock(blk.Copy());
            }

            if (returns)
            {
                ret.addReturn(raisesException);
            }

            return ret;
        }

        public override string ToString()
        {
            return procName;
        }

        // Return the trace that hasn't returned: either it is this one
        // (return null) or the last called trace
        private ErrorTrace getCurrTrace()
        {
            if (Blocks.Count == 0) return null;
            return Blocks[Blocks.Count - 1].getCurrTrace();
        }

        public static void printIndent(TokenTextWriter ttw, int indent)
        {
            for (int i = 0; i < indent; i++)
            {
                ttw.Write(" ");
            }
        }

        // Normalize tid values. Returns false if no tid information
        // (normalized or unnormalized) was found in the trace
        public static bool normalizeTid(ErrorTrace trace)
        {
            // fetch all tid values
            var vals = new HashSet<int>();
            collectTidInfo(trace, vals);

            // Sort values
            var vlist = new List<int>();
            vals.Iter(v => vlist.Add(v));
            vlist.Sort();

            // Build map to new values
            var newVal = new Dictionary<int, int>();
            int cnt = 1;
            foreach (var v in vlist)
            {
                newVal.Add(v, cnt);
                cnt++;
            }

            // Update values
            updateTidInfo(trace, newVal);

            return (newVal.Count != 0);
        }

        private static void updateTidInfo(ErrorTrace trace, Dictionary<int, int> newVal)
        {
            if (trace == null) return;
            foreach (var blk in trace.Blocks)
            {
                updateTid(blk.info, newVal);
                foreach (var inst in blk.Cmds)
                {
                    updateTid(inst.info, newVal);
                    if (inst.isCall())
                    {
                        updateTidInfo(inst.CalleeTrace, newVal);
                    }
                }
            }
        }


        private static void collectTidInfo(ErrorTrace trace, HashSet<int> vals)
        {
            if (trace == null) return;
            foreach (var blk in trace.Blocks)
            {
                fetchTid(blk.info, vals);
                foreach (var inst in blk.Cmds)
                {
                    fetchTid(inst.info, vals);
                    if (inst.isCall())
                    {
                        collectTidInfo(inst.CalleeTrace, vals);
                    }
                }
            }
        }

        public static void fillInContextSwitchInfo(ErrorTrace trace)
        {
            // We start with (k == 0, tid == 1) and push these down the trace, changing 
            // their values according to what is present in trace. We over-write
            // invalid info. Thread ID counter starts at 1 (0 is reserved for "no thread")
            tidCounter = 0;
            fillInContextSwitchInfo(trace, 0, getTid());
        }

        private static int fillInContextSwitchInfo(ErrorTrace trace, int k, int tid)
        {
            foreach (var blk in trace.Blocks)
            {
                fetchInfo(blk.info, ref k, ref tid);
                updateInfo(ref blk.info, k, tid);

                foreach (var inst in blk.Cmds)
                {
                    fetchInfo(inst.info, ref k, ref tid);
                    updateInfo(ref inst.info, k, tid);

                    if (inst.isCall())
                    {
                        CallInstr cinst = inst as CallInstr;
                        if (cinst.hasCalledTrace)
                        {
                            var oldk = k;

                            k = fillInContextSwitchInfo(cinst.calleeTrace, k,
                                cinst.asyncCall ? getTid() : tid);

                            if (cinst.asyncCall && cinst.calleeTrace.returns)
                            {
                                k = oldk;
                            }
                        }
                    }
                }
            }
            return k;
        }

        private static int tidCounter = 0;
        private static int getTid()
        {
            return ++tidCounter;
        }

        /*
        // Correct tid information so that "tid" is incremented only after 
        // a procedure call
        public static void correctTidInfoAtCalls(ErrorTrace trace)
        {
            int tid = 1;

            foreach (var blk in trace.Blocks)
            {
                if (blk.info != null && blk.info.tid >= 0)
                    tid = blk.info.tid;

                foreach (var c in blk.Cmds)
                {
                    if (!c.isCall() || (c.isCall() && !(c as CallInstr).asyncCall))
                    {
                        if (c.info != null && c.info.tid >= 0)
                            tid = c.info.tid;
                        continue;
                    }

                    var cc = c as CallInstr;
                    Debug.Assert(cc.asyncCall);
                    cc.info.tid = tid;

                    if (cc.calleeTrace != null)
                    {
                        correctTidInfoAtCalls(cc.calleeTrace);
                    }
                }
            }

        }
         */

        private static void fetchInfo(InstrInfo info, ref int k, ref int tid)
        {
            if (info == null)
                return;

            if (info.executionContext >= 0)
            {
                k = info.executionContext;
            }
            if (info.tid >= 0)
            {
                tid = info.tid;
            }
        }

        private static void updateInfo(ref InstrInfo info, int k, int tid)
        {
            if (info == null)
            {
                info = new InstrInfo(k, tid);
            }
            else
            {
                info.executionContext = k;
                info.tid = tid;
            }
        }

        private static void fetchTid(InstrInfo info, HashSet<int> vals)
        {
            if (info == null) return;
            if (info.tid >= 0) vals.Add(info.tid);
        }

        private static void updateTid(InstrInfo info, Dictionary<int, int> newVal)
        {
            if (info == null) return;
            if (info.tid < 0) return;
            info.tid = newVal[info.tid];
        }

        // Find the first occurance of "pred" along the trace
        public static Tuple<Implementation, Block, int> FindCmd(Program program, ErrorTrace trace, Predicate<Cmd> pred)
        {
            if (trace == null) return null;

            var impl = BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, trace.procName);
            var l2b = BoogieUtil.labelBlockMapping(impl);

            foreach (var tb in trace.Blocks)
            {
                var block = l2b[tb.blockName];
                for (int i = 0; i < Math.Min(block.Cmds.Count, tb.Cmds.Count); i++)
                {
                    if (pred(block.Cmds[i]))
                        return Tuple.Create(impl, block, i);
                }

                foreach (var ct in tb.Cmds.OfType<CallInstr>().Select(cc => cc.calleeTrace))
                {
                    var ret = FindCmd(program, ct, pred);
                    if (ret != null) return ret;
                }
            }

            return null;
        }
    }

    // A sequence of instruction through a basic block
    [Serializable]
    public class ErrorTraceBlock
    {
        // The block label
        public string blockName { get; private set; }

        // The sequence of instructions in the block
        public List<ErrorTraceInstr> Cmds { get; private set; }

        // Info for the block header
        public InstrInfo info;

        public ErrorTraceBlock(string name)
        {
            blockName = name;
            Cmds = new List<ErrorTraceInstr>();
            info = null;
        }

        // A block with the same instruction repeated a number of times
        public ErrorTraceBlock(string name, ErrorTraceInstr instr, int len)
        {
            blockName = name;
            Cmds = new List<ErrorTraceInstr>();
            for (int i = 0; i < len; i++)
            {
                Cmds.Add(instr);
            }
        }

        public override string ToString()
        {
            return blockName;
        }

        public bool isIntra()
        {
            foreach (var instr in Cmds)
            {
                if (instr.isCall())
                {
                    var cinstr = instr as CallInstr;
                    if (cinstr.hasCalledTrace)
                        return false;
                }
            }
            return true;
        }

        public void addInstr(ErrorTraceInstr instr)
        {
            Cmds.Add(instr);
        }

        public ErrorTraceBlock Copy()
        {
            var ret = new ErrorTraceBlock(blockName);
            if (info != null) ret.info = info.Copy();
            foreach (var inst in Cmds)
            {
                ret.addInstr(inst.Copy());
            }
            return ret;
        }

        // Delete the i^th instruction
        public ErrorTraceInstr delete(int i)
        {
            Debug.Assert(i >= 0 && i < Cmds.Count);
            var ret = Cmds[i];
            Cmds.RemoveAt(i);
            return ret;
        }

        public void printCalledTraces(TokenTextWriter ttw, string procName, int indent)
        {
            foreach (ErrorTraceInstr instr in Cmds)
            {
                if (instr.isCall())
                {
                    CallInstr cinstr = instr as CallInstr;
                    if (cinstr.hasCalledTrace)
                    {
                        cinstr.calleeTrace.printTrace(ttw, indent + 1);
                        if (cinstr.calleeTrace.returns)
                        {
                            ErrorTrace.printIndent(ttw, indent);
                            ttw.WriteLine(procName + ":" + blockName);
                        }
                    }
                }
            }
        }

        // Return the trace that hasn't returned: either it is this one
        // (return null) or the last called trace
        public ErrorTrace getCurrTrace()
        {
            if (Cmds.Count == 0) return null;
            var instr = Cmds[Cmds.Count - 1];

            if (instr.isCall())
            {
                var cinstr = instr as CallInstr;
                if (cinstr.Returns)
                    return null;
                return cinstr.calleeTrace;
            }
            else
            {
                return null;
            }
        }
    }

    // Interface for an instruction in an error trace. 
    [Serializable]
    abstract public class ErrorTraceInstr
    {
        [NonSerialized]
        public InstrInfo info;
        public virtual ErrorTrace CalleeTrace
        {
            get
            {
                return null;
            }
        }

        public ErrorTraceInstr()
        {
            info = new InstrInfo();
        }

        public ErrorTraceInstr(InstrInfo _info)
        {
            Debug.Assert(_info != null);
            info = _info;
        }

        abstract public ErrorTraceInstr Copy();
        abstract public bool isCall();
    }

    // A Call instruction
    [Serializable]
    public class CallInstr : ErrorTraceInstr
    {
        // This can be null -- indicating that a trace through
        // the callee is not available (possibly because it
        // has no implementation)
        public ErrorTrace calleeTrace { get; private set; }

        // Name of the called procedure
        public string callee;

        public override ErrorTrace CalleeTrace
        {
            get
            {
                return calleeTrace;
            }
        }

        // Is it an async call?
        public bool asyncCall { get; private set; }

        public static bool HwswSpecial = false;

        // Does the called trace return?
        public bool Returns
        {
            get
            {
                if (calleeTrace == null)
                    return true;
                return calleeTrace.returns;
            }
        }

        public bool hasCalledTrace
        {
            get
            {
                return (calleeTrace != null);
            }
        }

        public CallInstr(string callee)
            : this(callee, null, false, null)
        {

        }

        public CallInstr(ErrorTrace et)
            : this(et.procName, et, false, null)
        {

        }

        public CallInstr(ErrorTrace et, InstrInfo _info)
            : this(et.procName, et, false, _info)
        {
        }

        public CallInstr(ErrorTrace et, bool async, InstrInfo _info)
            : this(et.procName, et, async, _info)
        {
        }

        public CallInstr(string callee, ErrorTrace et, bool async, InstrInfo _info)
            : base()
        {
            if (_info != null) base.info = _info;
            this.callee = callee;
            calleeTrace = et;
            asyncCall = async;
            if (calleeTrace != null && !HwswSpecial)
            {
                Debug.Assert(calleeTrace.procName == callee);
            }
        }

        public override bool isCall()
        {
            return true;
        }

        public void SetErrorTrace(ErrorTrace ctrace)
        {
            calleeTrace = ctrace;
            if (calleeTrace != null)
                Debug.Assert(callee == calleeTrace.procName);
        }

        public override ErrorTraceInstr Copy()
        {
            InstrInfo ninfo = null;
            if (info != null) ninfo = info.Copy();

            if (calleeTrace == null)
                return new CallInstr(callee, null, asyncCall, ninfo);
            else
                return new CallInstr(callee, calleeTrace.Copy(), asyncCall, ninfo);
        }

        public override string ToString()
        {
            if (hasCalledTrace)
            {
                return string.Format("{0}call({1})", asyncCall ? "async " : "", calleeTrace.ToString());
            }
            else
            {
                return "call " + callee;
            }
        }
    }

    // A non-call instruction
    [Serializable]
    public class IntraInstr : ErrorTraceInstr
    {
        public IntraInstr() : base() { }

        public IntraInstr(InstrInfo _info)
            : base(_info)
        {
        }

        public override bool isCall()
        {
            return false;
        }

        public override ErrorTraceInstr Copy()
        {
            InstrInfo ninfo = null;
            if (info != null) ninfo = info.Copy();

            return new IntraInstr(ninfo);
        }

        public override string ToString()
        {
            return "Intra";
        }
    }

    // Some information attached to an instruction
    [Serializable]
    public class InstrInfo
    {
        // The execution context under which the instruction fires.
        public int executionContext
        {
            get
            {
                return (int)varToVal["k"];
            }
            set
            {
                varToVal["k"] = value;
            }
        }

        // The thread ID under which the instruction fires.
        public int tid
        {
            get
            {
                return (int)varToVal[LanguageSemantics.tidName];
            }
            set
            {
                varToVal[LanguageSemantics.tidName] = value;
            }
        }

        // Variable name to value 
        protected Dictionary<string, object> varToVal;

        public bool isValid
        {
            get
            {
                return (executionContext >= 0) || (tid >= 0);
            }
        }

        public InstrInfo()
        {
            varToVal = new Dictionary<string, object>();
            varToVal.Add("k", -1);
            varToVal.Add(LanguageSemantics.tidName, -1);
        }

        public InstrInfo(InstrInfo c)
        {
            if (c == null)
            {
                varToVal = new Dictionary<string, object>();
                varToVal.Add("k", -1);
                varToVal.Add(LanguageSemantics.tidName, -1);
            }
            else
            {
                varToVal = new Dictionary<string, object>(c.varToVal);
            }
        }

        public InstrInfo(int _executionContext, int _tid) :
            this()
        {
            executionContext = _executionContext;
            tid = _tid;
        }

        public void addVal(string var, object val)
        {
            if (var == "k" || var == LanguageSemantics.tidName)
            {
                if (val is Microsoft.BaseTypes.BigNum)
                {
                    val = BoogieUtil.BigNumToIntForce((Microsoft.BaseTypes.BigNum)val);
                }
            }

            if (varToVal.ContainsKey(var))
            {
                varToVal[var] = val;
            }
            else
            {
                varToVal.Add(var, val);
            }
        }

        public object getVal(string var)
        {
            Debug.Assert(varToVal.ContainsKey(var));
            return varToVal[var];
        }

        public int getIntVal(string var)
        {
            var val = getVal(var);
            if (val is int) return (int)val;
            if (val is Model.Integer) return ((Model.Integer)val).AsInt();
            if (val is Microsoft.BaseTypes.BigNum) return BoogieUtil.BigNumToIntForce((Microsoft.BaseTypes.BigNum)val);
            Debug.Assert(false);
            return 0;
        }

        public bool getBoolVal(string var)
        {
            var val = getVal(var);
            if (val is bool) return (bool)val;
            if (val is Model.Boolean) return ((Model.Boolean)val).Value;
            Debug.Assert(false);
            return false;
        }

        public Microsoft.BaseTypes.BigNum getBigNumVal(string var)
        {
            var val = getVal(var);
            if (val is int) return Microsoft.BaseTypes.BigNum.FromInt((int)val);
            if (val is Model.Integer) return Microsoft.BaseTypes.BigNum.FromString(((Model.Integer)val).Numeral);
            if (val is Microsoft.BaseTypes.BigNum) return (Microsoft.BaseTypes.BigNum)val;
            Debug.Assert(false);
            return Microsoft.BaseTypes.BigNum.FromInt(0);
        }


        public bool hasVar(string var)
        {
            return varToVal.ContainsKey(var);
        }

        public bool hasIntVar(string var)
        {
            if (!hasVar(var)) return false;
            var v = varToVal[var];
            return ((v is int) || (v is Microsoft.Boogie.Model.Integer) ||
                (v is Microsoft.BaseTypes.BigNum));
        }

        public bool hasBoolVar(string var)
        {
            if (!hasVar(var)) return false;
            var v = varToVal[var];
            return ((v is bool) || (v is Microsoft.Boogie.Model.Boolean));
        }

        public override string ToString()
        {
            var ret = "";
            foreach (var tp in varToVal)
            {
                if (tp.Key == "k" && ((int)tp.Value) == -1) continue;
                if (tp.Key == LanguageSemantics.tidName && ((int)tp.Value) == -1) continue;
                ret += string.Format("{0}={1} ", tp.Key, tp.Value.ToString());
            }
            return ret;
        }

        public virtual InstrInfo Copy()
        {
            var ret = new InstrInfo();
            ret.varToVal = new Dictionary<string, object>(varToVal);
            return ret;
        }

        public void removeVar(string varName)
        {
            if (varToVal.ContainsKey(varName)) varToVal.Remove(varName);
        }
    }

    // Marks a failing assert
    [Serializable]
    public class AssertFailInstrInfo : InstrInfo
    {
        public AssertFailInstrInfo() : base() { }
        public AssertFailInstrInfo(InstrInfo info) : base(info) { }

        public override InstrInfo Copy()
        {
            var ret = new AssertFailInstrInfo();
            ret.varToVal = new Dictionary<string, object>(varToVal);
            return ret;
        }
    }

    // Marks a failing requires
    [Serializable]
    public class RequiresFailInstrInfo : AssertFailInstrInfo
    {
        public RequiresFailInstrInfo() : base() { }
        public RequiresFailInstrInfo(InstrInfo info) : base(info) { }

        public override InstrInfo Copy()
        {
            var ret = new RequiresFailInstrInfo();
            ret.varToVal = new Dictionary<string, object>(varToVal);
            return ret;
        }
    }

    // Marks a failing ensures
    [Serializable]
    public class EnsuresFailInstrInfo : AssertFailInstrInfo
    {
        public EnsuresFailInstrInfo() : base() { }
        public EnsuresFailInstrInfo(InstrInfo info) : base(info) { }

        public override InstrInfo Copy()
        {
            var ret = new EnsuresFailInstrInfo();
            ret.varToVal = new Dictionary<string, object>(varToVal);
            return ret;
        }
    }

    // For storing data values
    [Serializable]
    public class ModelInstrInfo : InstrInfo, ISerializable
    {
        public int index { get; private set; }
        public Model model { get; private set; }
        // a pointer to model.States[index]
        Model.CapturedState state;

        public ModelInstrInfo() : base()
        {
            index = -1;
        }

        public ModelInstrInfo(InstrInfo info) : base(info) { }

        public ModelInstrInfo(Model model, int index)
            : base()
        {
            this.index = index;
            this.model = model;
            this.state = model.States.ElementAt(index);
            this.state.ChangeName("CorralState_" + index.ToString());
        }

        public override InstrInfo Copy()
        {
            var ret = new ModelInstrInfo(model, index);
            ret.varToVal = new Dictionary<string, object>(varToVal);
            return ret;
        }

        public override string ToString()
        {
            //var st = base.ToString();
            return "CorralState_" + index.ToString();
        }
        #region Serializability Members
        public void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            info.AddValue("index", index);
        }
        /*
         * 
         *The deserializer is only used in traceAnalyser and we dont need the model and state there!
         */
        public ModelInstrInfo(SerializationInfo info, StreamingContext context)
        {
            index = info.GetInt32("index");
            model = null;
            state = null;
        }
        #endregion
    }

    // If one wants the info to be printed in an error trace
    [Serializable]
    public class PrintInstrInfo : InstrInfo
    {
        public PrintInstrInfo(InstrInfo info) :
            base(info)
        { }

        public override InstrInfo Copy()
        {
            return new PrintInstrInfo(base.Copy());
        }
    }

}

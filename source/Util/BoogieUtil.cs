using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;

namespace cba.Util
{
    public class BoogieUtil
    {
        public static CommandLineOptions BoogieOptions = null;
        public static int RecursionBound = 1;

        public static bool InitializeBoogie(string clo)
        {
            BoogieOptions.RunningBoogieFromCommandLine = true;

            var quotes = (" " + clo + " ").Split(new char[] { '\"' }, StringSplitOptions.RemoveEmptyEntries);
            var args = new List<string>();
            // for every odd i, quotes[i] appears inside quotes
            for (int i = 0; i < quotes.Length; i++)
            {
                if (i % 2 == 0)
                    args.AddRange(quotes[i].Split(new char[] { ' ' }, StringSplitOptions.RemoveEmptyEntries));
                else
                    args.Add(quotes[i]);
            }

            if (!BoogieOptions.Parse(args.ToArray()))
                return true;

            return false;
        }

        public static void DoModSetAnalysis(Program p)
        {
            var procByName = p.TopLevelDeclarations.OfType<Procedure>()
                .ToDictionary(proc => proc.Name);
            foreach (var impl in p.TopLevelDeclarations.OfType<Implementation>())
            {
                if (procByName.TryGetValue(impl.Name, out var implProc))
                {
                    impl.Proc = implProc;
                }

                foreach (var block in impl.Blocks)
                {
                    foreach (var cmd in block.Cmds.OfType<CallCmd>())
                    {
                        if (procByName.TryGetValue(cmd.callee, out var proc))
                        {
                            cmd.Proc = proc;
                        }
                    }
                }
            }
            (new ModSetCollector(BoogieOptions)).CollectModifies(p);

            // Boogie 3.5.6's ModSetCollector appends to each procedure's existing
            // modifies list, deduplicating by Variable object identity
            // (Core/Analysis/ModSetCollector.cs). Boogie 2.9.1 instead replaced the
            // list outright (Core/DeadVarElim.cs), which could not produce duplicates
            // and also severed any aliasing of the old list. Restore that guarantee:
            // CallCmd.ComputeDesugaring builds a Dictionary keyed on the modified
            // variable and throws ArgumentException on a duplicate -- its own comment
            // records the assumption ("this assumes no duplicates in this.Proc.Modifies").
            // On real SMACK input the duplicates come from stale cross-program
            // Decl pointers rather than from a shared list. Measured on
            // bench/bpl-u4 with SMACK's flags, the instrumented main arrives here
            // with every modifies entry pointing at a *previous* program's
            // GlobalVariable objects -- same names, different instances -- so the
            // identity comparison matches nothing and a full second copy is
            // appended:
            //     parport_false.i.cil   main_SeqInstr  59 -> 119  (59/59 foreign)
            //     pointers_fail         main_SeqInstr   2 ->   5  (2/2 foreign)
            // Duplicates can also arrive straight from the input text, since
            // InferModifies=true disables the resolver's modifies check.
            foreach (var proc in p.TopLevelDeclarations.OfType<Procedure>())
            {
                if (proc.Modifies == null || proc.Modifies.Count < 2)
                    continue;
                var seen = new HashSet<string>();
                var deduped = new List<IdentifierExpr>();
                foreach (var ie in proc.Modifies)
                {
                    if (seen.Add(ie.Decl != null ? ie.Decl.Name : ie.Name))
                        deduped.Add(ie);
                }
                if (deduped.Count != proc.Modifies.Count)
                    proc.Modifies = deduped;
            }
        }

        public static void PrintProgram(Program p, string filename)
        {
            var outFile = new TokenTextWriter(filename, BoogieOptions);
            p.Emit(outFile);
            outFile.Close();
        }

        public static bool ResolveProgram(Program p, string filename)
        {
            int errorCount = ResolveProgram(p);
            if (errorCount != 0)
                Console.WriteLine(errorCount + " name resolution errors in " + filename);
            return errorCount != 0;
        }

        public static bool TypecheckProgram(Program p, string filename)
        {
            int errorCount = TypecheckProgram(p);
            if (errorCount != 0)
            {
                PrintProgram(p, "error.bpl");
                Console.WriteLine(errorCount + " type checking errors in " + filename);
            }
            return errorCount != 0;
        }

        public static int ResolveProgram(Program p)
        {
            return WithLegacyAsyncCallsDisabled(p, () => p.Resolve(BoogieOptions));
        }

        public static int TypecheckProgram(Program p)
        {
            return WithLegacyAsyncCallsDisabled(p, () => p.Typecheck(BoogieOptions));
        }

        private static int WithLegacyAsyncCallsDisabled(Program p, Func<int> action)
        {
            var asyncCalls = p.TopLevelDeclarations
                .OfType<Implementation>()
                .SelectMany(impl => impl.Blocks)
                .SelectMany(block => block.Cmds)
                .OfType<CallCmd>()
                .Where(cmd => cmd.IsAsync)
                .ToList();

            foreach (var cmd in asyncCalls)
            {
                cmd.IsAsync = false;
            }

            try
            {
                return action();
            }
            finally
            {
                foreach (var cmd in asyncCalls)
                {
                    cmd.IsAsync = true;
                }
            }
        }

        public static HashSet<string> getGlobalVarsModified(Cmd cmd, HashSet<string> procsWithImpl)
        {
            var ret = new HashSet<string>();

            if (cmd is HavocCmd)
            {
                var hcmd = cmd as HavocCmd;
                foreach (IdentifierExpr v in hcmd.Vars)
                {
                    if (v.Decl is GlobalVariable)
                    {
                        ret.Add(v.Decl.Name);
                    }
                }
                return ret;
            }
            else if (cmd is CallCmd)
            {
                var ccmd = cmd as CallCmd;
                foreach (IdentifierExpr v in ccmd.Outs)
                {
                    if (v.Decl is GlobalVariable) ret.Add(v.Decl.Name);
                }

                if (procsWithImpl.Contains(ccmd.Proc.Name))
                    return ret;

                foreach (IdentifierExpr v in ccmd.Proc.Modifies)
                {
                    if (v.Decl is GlobalVariable)
                    {
                        ret.Add(v.Decl.Name);
                    }
                }
                return ret;
            }
            else if (cmd is AssignCmd)
            {
                var acmd = cmd as AssignCmd;
                Debug.Assert(acmd.Lhss.Count == 1);
                var v = acmd.Lhss[0].DeepAssignedVariable;
                if (v is GlobalVariable)
                    ret.Add(v.Name);
                return ret;
            }
            else
            {
                return ret;
            }
        }

        // Prune by removing procedures that are not called
        public static void pruneProcs(Program program, string mainProcName)
        {
            if (mainProcName == null)
                return;

            pruneProcs(program, new HashSet<string> { mainProcName });
        }

        public static void pruneProcs(Program program, HashSet<string> mains)
        {
            var edges = new Dictionary<string, HashSet<string>>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                var impl = decl as Implementation;
                if (impl == null) continue;
                edges.Add(impl.Name, new HashSet<string>());
                foreach (var blk in impl.Blocks)
                {
                    blk.Cmds.OfType<CallCmd>()
                        .Iter(ccmd => edges[impl.Name].Add(ccmd.callee));
                    blk.Cmds.OfType<ParCallCmd>()
                        .Iter(pcmd => pcmd.CallCmds
                            .Iter(ccmd => edges[impl.Name].Add(ccmd.callee)));
                }
            }
            var reachable = new HashSet<string>();
            reachable.UnionWith(mains);

            var delta = new HashSet<string>(reachable);
            while (delta.Count != 0)
            {
                var nf = new HashSet<string>();
                foreach (var n in delta)
                {
                    if (edges.ContainsKey(n)) nf.UnionWith(edges[n]);
                }
                delta = nf.Difference(reachable);
                reachable.UnionWith(nf);
            }

            var allProcs = new HashSet<string>(edges.Keys);
            var toRemove = allProcs.Difference(reachable);

            var newDecls = new List<Declaration>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                if (decl is Procedure && toRemove.Contains((decl as Procedure).Name)) continue;
                if (decl is Implementation && toRemove.Contains((decl as Implementation).Name)) continue;
                newDecls.Add(decl);
            }
            program.TopLevelDeclarations = newDecls;
        }

        // Return the set of procedures that may reach a cmd that satisfies pred
        public static HashSet<string> procsThatMaySatisfyPredicate(Program program, Predicate<Cmd> pred)
        {
            // target procedures
            var targets = new HashSet<string>();

            // call graph
            var edges = new Dictionary<string, HashSet<string>>();
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    blk.Cmds.OfType<CallCmd>()
                        .Iter(ccmd => edges.InitAndAdd(ccmd.callee, impl.Name));
                    blk.Cmds.OfType<ParCallCmd>()
                        .Iter(pcmd => pcmd.CallCmds
                            .Iter(ccmd => edges.InitAndAdd(ccmd.callee, impl.Name)));
                    if (blk.Cmds.Any(c => pred(c)))
                        targets.Add(impl.Name);
                }
            }
            var reachable = new HashSet<string>(targets);

            var delta = new HashSet<string>(reachable);
            while (delta.Count != 0)
            {
                var nf = new HashSet<string>();
                foreach (var n in delta)
                {
                    if (edges.ContainsKey(n)) nf.UnionWith(edges[n]);
                }
                delta = nf.Difference(reachable);
                reachable.UnionWith(nf);
            }

            return reachable;
        }

        // Call graph over implementations
        public static Graph<string> GetCallGraph(Program program)
        {
            var graph = new Graph<string>();
            var impls = new HashSet<string>(program.TopLevelDeclarations.OfType<Implementation>().Select(impl => impl.Name));
            impls.Iter(p => graph.Nodes.Add(p));

            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                impl.Blocks
                    .Iter(blk => blk.Cmds
                        .OfType<CallCmd>()
                        .Where(cc => impls.Contains(cc.callee))
                        .Iter(cc => graph.AddEdge(impl.Name, cc.callee)));
            }
            return graph;
        }

        // Return nodes on some cycle
        public static HashSet<Node> GetCyclicNodes<Node>(Graph<Node> graph) where Node : class
        {
            var ret = new HashSet<Node>();
            var scc = new StronglyConnectedComponents<Node>(graph.Nodes,
                new Adjacency<Node>(n => graph.Predecessors(n)), new Adjacency<Node>(n => graph.Successors(n)));
            scc.Compute();

            foreach (var s in scc)
            {
                if (s.Count == 0) continue;

                if (s.Count > 1 || graph.Successors(s.First()).Contains(s.First()))
                {
                    ret.UnionWith(s);
                }
            }

            return ret;
        }

        // Get reachable nodes
        public static HashSet<Node> GetReachableNodes<Node>(Node n, Graph<Node> graph) where Node : class
        {
            return GetReachableNodes<Node>(new HashSet<Node> { n }, graph);
        }

        public static HashSet<Node> GetReachableNodes<Node>(HashSet<Node> source, Graph<Node> graph) where Node : class
        {
            var ret = new HashSet<Node>(source);
            var frontier = new HashSet<Node>(source);

            while (frontier.Count > 0)
            {
                var next = new HashSet<Node>();
                frontier.Iter(v => next.UnionWith(graph.Successors(v)));
                next.ExceptWith(ret);
                ret.UnionWith(next);
                frontier = next;
            }
            return ret;
        }
        public static HashSet<string> getVarsModified(Cmd cmd, HashSet<string> procsWithImpl)
        {
            var ret = new HashSet<string>();

            if (cmd is HavocCmd)
            {
                var hcmd = cmd as HavocCmd;
                foreach (IdentifierExpr v in hcmd.Vars)
                {
                    ret.Add(v.Decl.Name);
                }
                return ret;
            }
            else if (cmd is CallCmd)
            {
                var ccmd = cmd as CallCmd;
                foreach (IdentifierExpr v in ccmd.Outs)
                {
                    if (v != null) ret.Add(v.Decl.Name);
                }

                if (procsWithImpl.Contains(ccmd.Proc.Name))
                    return ret;

                foreach (IdentifierExpr v in ccmd.Proc.Modifies)
                {
                    ret.Add(v.Decl.Name);
                }
                return ret;
            }
            else if (cmd is AssignCmd)
            {
                var acmd = cmd as AssignCmd;
                foreach (var ae in acmd.Lhss)
                {
                    var v = ae.DeepAssignedVariable;
                    ret.Add(v.Name);
                }
                return ret;
            }
            else
            {
                return ret;
            }
        }

        public static int BigNumToIntForce(Microsoft.BaseTypes.BigNum num)
        {
            if (num.InInt32) return num.ToInt;
            if (num > Microsoft.BaseTypes.BigNum.FromInt(0)) return int.MaxValue;
            return int.MinValue;
        }

        // Remove attribute "name" from the list
        public static QKeyValue removeAttr(string name, QKeyValue attr)
        {
            if (attr == null) return null;
            var tail = removeAttr(name, attr.Next);
            if (attr.Key == name) return tail;
            return new QKeyValue(attr.tok, attr.Key, attr.Params, tail);
        }

        // Remove attributes "name" from the list
        public static QKeyValue removeAttrs(HashSet<string> name, QKeyValue attr)
        {
            if (attr == null) return null;
            var tail = removeAttrs(name, attr.Next);
            if (name.Contains(attr.Key)) return tail;
            return new QKeyValue(attr.tok, attr.Key, attr.Params, tail);
        }

        // Is there a Key called "name"
        public static IList<object> getAttr(string name, QKeyValue attr)
        {
            for (; attr != null; attr = attr.Next)
            {
                if (attr.Key == name) return attr.Params;
            }
            return null;
        }

        // Is there a Key called "name"
        public static bool checkAttrExists(string name, QKeyValue attr)
        {
            for (; attr != null; attr = attr.Next)
            {
                if (attr.Key == name) return true;
            }
            return false;
        }

        // Is there a Key called "name"
        public static bool checkAttrExists(HashSet<string> name, QKeyValue attr)
        {
            for (; attr != null; attr = attr.Next)
            {
                if (name.Contains(attr.Key)) return true;
            }
            return false;
        }


        public static Program ParseProgram(string f)
        {
            Program p = new Program();

            try
            {
                if (Parser.Parse(f, new List<string>(), out p) != 0)
                {
                    Console.WriteLine("Failed to read " + f);
                    return null;
                }
            }
            catch (Exception e)
            {
                Console.WriteLine(e.ToString());
                return null;
            }
            return p;
        }

        public static Program ReadAndResolve(string filename, bool doTypecheck = true)
        {
            Program p = ParseProgram(filename);

            if (p == null)
            {
                throw new InvalidProg("Parse errors in " + filename);
            }

            if (ResolveProgram(p, filename))
            {
                throw new InvalidProg("Cannot resolve " + filename);
            }
            if (doTypecheck && TypecheckProgram(p, filename))
            {
                throw new InvalidProg("Cannot typecheck " + filename);
            }

            return p;
        }

        public static Program ReadAndOnlyResolve(string filename)
        {
            Program p = ParseProgram(filename);

            if (p == null)
            {
                throw new InvalidProg("Parse errors in " + filename);
            }

            if (ResolveProgram(p, filename))
            {
                throw new InvalidProg("Cannot resolve " + filename);
            }

            DesugarUnpackCmds(p);

            return p;
        }

        // Replace "C(x, y) := e" with Boogie's own desugaring of it:
        //   assert is#C(e);  x, y := e->f1, e->f2;
        // Boogie 3.5.6 added UnpackCmd, and nothing in corral knows about it:
        // variable slicing rejects the command outright, and the assertion it
        // carries would never reach RewriteAssertsPass, so a failing unpack could
        // not be reported. Desugaring as the program is read keeps every later
        // pass seeing only the commands corral was written against. It belongs
        // here rather than at one call site because the trace printer re-reads the
        // input file and lines its commands up with the verified program index by
        // index; the two views have to expand identically.
        private static void DesugarUnpackCmds(Program program)
        {
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var block in impl.Blocks)
                {
                    if (!block.Cmds.OfType<UnpackCmd>().Any())
                        continue;

                    var newCmds = new List<Cmd>();
                    foreach (var cmd in block.Cmds)
                    {
                        if (cmd is UnpackCmd ucmd &&
                            ucmd.GetDesugaring(BoogieOptions) is StateCmd desugared)
                        {
                            impl.LocVars.AddRange(desugared.Locals);
                            newCmds.AddRange(desugared.Cmds);
                        }
                        else
                        {
                            newCmds.Add(cmd);
                        }
                    }
                    block.Cmds = newCmds;
                }
            }
        }

        // Prints the program into a file, reads it back in, parses it,
        // resolves it and typechecks it
        public static Program ReResolve(Program p, bool doTypecheck = true)
        {
            return ReResolve(p, "temp_rar.bpl", doTypecheck);
        }

        public static Program ReResolveInMem(Program p, bool doTypecheck = true)
        {
            Program output;
            using (var writer = new System.IO.MemoryStream())
            {
                var st = new System.IO.StreamWriter(writer);
                var tt = new TokenTextWriter(st, BoogieOptions);
                p.Emit(tt);
                writer.Flush();
                st.Flush();

                writer.Seek(0, System.IO.SeekOrigin.Begin);
                var s = ParserHelper.Fill(writer, new List<string>());

                var v = Parser.Parse(s, "ReResolveInMem", out output);
                if (ResolveProgram(output, "ReResolveInMem"))
                {
                    throw new InvalidProg("Cannot resolve " + "ReResolveInMem");
                }
                if (doTypecheck && TypecheckProgram(output, "ReResolveInMem"))
                {
                    throw new InvalidProg("Cannot typecheck " + "ReResolveInMem");
                }
            }
            return output;
        }

        // Prints the program into a file, reads it back in, parses it,
        // resolves it and typechecks it
        public static Program ReResolve(Program p, string filename, bool doTypecheck = true)
        {
            PrintProgram(p, filename);
            return ReadAndResolve(filename, doTypecheck);
        }

        public static void PrintGlobalVariables(Program p)
        {
            TokenTextWriter log = new TokenTextWriter(Console.Out, BoogieOptions);
            foreach (Declaration d in p.TopLevelDeclarations)
            {
                if (d is GlobalVariable)
                    d.Emit(log, 0);
            }
        }

        public static IEnumerable<GlobalVariable> GetGlobalVariables(Program p)
        {
            return p.TopLevelDeclarations.OfType<GlobalVariable>();
        }

        public static List<GlobalVariable> GetModifiedGlobalVariables(Program p)
        {
            var ret = new List<GlobalVariable>();
            var seen = new HashSet<string>();
            foreach (var proc in GetProcedures(p))
            {
                foreach (IdentifierExpr ie in proc.Modifies)
                {
                    var v = ie.Decl as GlobalVariable;
                    if (!seen.Contains(v.Name))
                    {
                        ret.Add(v);
                        seen.Add(v.Name);
                    }
                }
            }
            return ret;
        }

        public static IEnumerable<Procedure> GetProcedures(Program p)
        {
            return p.TopLevelDeclarations.OfType<Procedure>();
        }

        public static HashSet<string> GetAllProcNames(Program p)
        {
            var ret = new HashSet<string>();
            p.TopLevelDeclarations.OfType<Procedure>().Iter(x => ret.Add((x as Procedure).Name));
            return ret;
        }

        public static HashSet<string> GetAllImplNames(Program p)
        {
            var ret = new HashSet<string>();
            p.TopLevelDeclarations.OfType<Implementation>().Iter(x => ret.Add((x as Implementation).Name));
            return ret;
        }

        public static IEnumerable<Implementation> GetImplementations(Program p)
        {
            return p.TopLevelDeclarations.OfType<Implementation>();
        }

        public static GlobalVariable findVarDecl(IEnumerable<Declaration> decls, string varname)
        {
            foreach (Declaration d in decls)
            {
                if (d is GlobalVariable)
                {
                    if ((d as GlobalVariable).Name.Equals(varname))
                        return (d as GlobalVariable);
                }
            }
            return null;
        }

        public static Procedure findProcedureDecl(IEnumerable<Declaration> decls, string procname)
        {
            foreach (Declaration d in decls)
            {
                if (d is Procedure)
                {
                    if ((d as Procedure).Name.Equals(procname))
                        return (d as Procedure);
                }
            }
            return null;
        }

        public static Implementation findProcedureImpl(IEnumerable<Declaration> decls, string procname)
        {
            foreach (Declaration d in decls)
            {
                if (d is Implementation)
                {
                    if ((d as Implementation).Name.Equals(procname))
                        return (d as Implementation);
                }
            }

            return null;
        }

        // Constructs a mapping from labels to blocks of an implementation
        public static Dictionary<string, Block> labelBlockMapping(Implementation impl)
        {
            var blocks = new Dictionary<string, Block>();
            foreach (Block b in impl.Blocks)
            {
                blocks.Add(b.Label, b);
            }

            return blocks;
        }

        // Constructs a mapping from procedure names to the implementation
        public static Dictionary<string, Implementation> nameImplMapping(Program p)
        {
            var m = new Dictionary<string, Implementation>();
            foreach (Declaration d in p.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    Implementation impl = d as Implementation;
                    m.Add(impl.Name, impl);
                }
            }

            return m;
        }

        // Constructs a mapping from procedure names to the Procedure
        public static Dictionary<string, Procedure> nameProcMapping(Program p)
        {
            var m = new Dictionary<string, Procedure>();
            foreach (Declaration d in p.TopLevelDeclarations)
            {
                if (d is Procedure)
                {
                    Procedure proc = d as Procedure;
                    m.Add(proc.Name, proc);
                }
            }

            return m;
        }

        public static double GetMemUsage()
        {
            var p = System.Diagnostics.Process.GetCurrentProcess();
            return p.VirtualMemorySize64 / (1024.0 * 1024.0);
        }


        // is this a non-trivial assert? 
        public static bool isAssert(Cmd cmd)
        {
            var acmd = cmd as AssertCmd;
            if (acmd == null || isAssertTrue(cmd)) return false;
            return true;
        }

        // is "assert true"?
        public static bool isAssertTrue(Cmd cmd)
        {
            var acmd = cmd as AssertCmd;
            if (acmd == null) return false;
            var le = acmd.Expr as LiteralExpr;
            if (le == null) return false;
            if (le.IsTrue) return true;
            return false;
        }

        // is "assume false"?
        public static bool isAssumeFalse(Cmd cmd)
        {
            var acmd = cmd as AssumeCmd;
            if (acmd == null) return false;
            var le = acmd.Expr as LiteralExpr;
            if (le == null) return false;
            if (le.IsFalse) return true;
            return false;
        }

        // check if the command cmd is "call name(...)"
        public static bool checkIsCall(string name, Cmd cmd)
        {
            if (name.Equals(""))
                return false;

            if (cmd is CallCmd)
            {
                CallCmd ccmd = (CallCmd)cmd;
                if (ccmd.Proc.Name.Equals(name))
                    return true;
            }

            return false;
        }

        // Does the implementation have an assert command
        public static bool hasAssert(Implementation impl)
        {
            foreach (Block blk in impl.Blocks)
            {
                foreach (Cmd cmd in blk.Cmds)
                {
                    if (cmd is AssertCmd)
                        return true;
                }
            }
            return false;
        }
    }

    public class BoogieAstFactory
    {
        public static List<Declaration> newDecls = new List<Declaration>();

        static int uniqueInt = 0;
        public static string uniqueLabel()
        {
            return "L_BAF_" + (uniqueInt++);
        }

        static Dictionary<Duple<string, int>, Function> BVOperations = new Dictionary<Duple<string, int>, Function>();

        public static Function getBVOperation(string op, int bits)
        {
            var key = new Duple<string, int>(op, bits);
            if (BVOperations.ContainsKey(key))
            {
                return BVOperations[key];
            }
            var bvtype = Microsoft.Boogie.Type.GetBvType(bits);

            var arg1 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", bvtype), true);
            var arg2 = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", bvtype), true);
            var args = new List<Variable>();
            args.Add(arg1);
            args.Add(arg2);

            var res = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", Microsoft.Boogie.Type.Bool), false);
            var ret = new Function(Token.NoToken, string.Format("Corral_bv_{0}_{1}", op, bits), args, res);

            var aval = new List<object>();
            aval.Add(op);
            ret.Attributes = new QKeyValue(Token.NoToken, "bvbuiltin", aval, null);

            BVOperations.Add(key, ret);
            newDecls.Add(ret);

            return ret;
        }

        // var := const
        public static AssignCmd MkVarEqConst(Variable v, int c)
        {

            AssignLhs lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(v.tok, v));
            Expr rhs = Expr.Literal(c);
            var temp1 = new List<AssignLhs>();
            var temp2 = new List<Expr>();
            temp1.Add(lhs);
            temp2.Add(rhs);
            return new AssignCmd(Token.NoToken, temp1, temp2);
        }

        // var := expr
        public static AssignCmd MkVarEqExpr(Variable v, Expr rhs)
        {
            AssignLhs lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(v.tok, v));

            var temp1 = new List<AssignLhs>();
            var temp2 = new List<Expr>();
            temp1.Add(lhs);
            temp2.Add(rhs);
            return new AssignCmd(Token.NoToken, temp1, temp2);
        }

        // var1 := var2
        public static AssignCmd MkVarEqVar(Variable v1, Variable v2)
        {
            AssignLhs lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(v1.tok, v1));

            var temp1 = new List<AssignLhs>();
            var temp2 = new List<Expr>();
            temp1.Add(lhs);
            temp2.Add(Expr.Ident(v2));
            return new AssignCmd(Token.NoToken, temp1, temp2);
        }

        // var := const
        public static AssignCmd MkVarEqConst(Variable v, bool c)
        {

            AssignLhs lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(v.tok, v));
            Expr rhs = Expr.Literal(c);
            var temp1 = new List<AssignLhs>();
            var temp2 = new List<Expr>();
            temp1.Add(lhs);
            temp2.Add(rhs);
            return new AssignCmd(Token.NoToken, temp1, temp2);
        }

        // var := var && acmd
        public static AssignCmd instrumentAssert(Variable v, AssertCmd acmd)
        {
            AssignLhs lhs = new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(v.tok, v));
            Expr rhs = Expr.And(Expr.Ident(v), acmd.Expr);

            var temp1 = new List<AssignLhs>();
            var temp2 = new List<Expr>();
            temp1.Add(lhs);
            temp2.Add(rhs);
            return new AssignCmd(Token.NoToken, temp1, temp2);
        }

        // assume c --->  assume (k == i) => c
        public static AssumeCmd instrumentAssume(AssumeCmd acmd, Variable k, int i)
        {
            var temp1 = Expr.Eq(Expr.Ident(k), Expr.Literal(i));
            var temp2 = Expr.Imp(temp1, acmd.Expr);
            return new AssumeCmd(acmd.tok, temp2);
        }

        // var < const
        public static AssumeCmd MkAssumeVarLtConst(Variable v, int c)
        {
            Expr temp1 = Expr.Ident(v);
            Expr temp2 = Expr.Literal(c);
            return new AssumeCmd(Token.NoToken, Expr.Lt(temp1, temp2));
        }

        // var >= const
        public static AssumeCmd MkAssumeVarGeConst(Variable v, int c)
        {
            Expr temp1 = Expr.Ident(v);
            Expr temp2 = Expr.Literal(c);
            return new AssumeCmd(Token.NoToken, Expr.Ge(temp1, temp2));
        }

        // var > const
        public static AssumeCmd MkAssumeVarGtConst(Variable v, int c)
        {
            Expr temp1 = Expr.Ident(v);
            Expr temp2 = Expr.Literal(c);
            return new AssumeCmd(Token.NoToken, Expr.Gt(temp1, temp2));
        }

        // var1 > var2
        public static AssumeCmd MkAssumeVarGtVar(Variable v1, Variable v2)
        {
            if (v1.TypedIdent.Type.IsInt)
            {
                Expr temp1 = Expr.Ident(v1);
                Expr temp2 = Expr.Ident(v2);
                //var t = new NAryExpr(Token.NoToken, new FunctionCall(), 
                return new AssumeCmd(Token.NoToken, Expr.Gt(temp1, temp2));
            }
            else if (v1.TypedIdent.Type.IsBv)
            {
                Expr temp1 = Expr.Ident(v1);
                Expr temp2 = Expr.Ident(v2);
                var args = new List<Expr>();
                args.Add(temp1);
                args.Add(temp2);
                var fun = getBVOperation("bvugt", v1.TypedIdent.Type.BvBits);
                var funcall = new FunctionCall(fun);

                return new AssumeCmd(Token.NoToken, new NAryExpr(Token.NoToken, funcall, args));
            }
            else
            {
                Debug.Assert(false);
                return null;
            }
        }

        // var1 > var2
        public static Expr MkExprVarGtVar(Variable v1, Variable v2)
        {
            return MkAssumeVarGtVar(v1, v2).Expr;
        }

        // var1 >= var2
        public static Expr MkExprVarGeVar(Variable v1, Variable v2)
        {
            return Expr.Ge(Expr.Ident(v1), Expr.Ident(v2));
        }


        public static Expr MkExprAnd(params Expr[] e)
        {
            Expr ret = Expr.True;
            e.Iter(expr => { ret = Expr.And(ret, expr); });
            return ret;
        }

        // old(var1) <= var2
        public static AssumeCmd MkAssumeOldVarLeVar(Variable v1, Variable v2)
        {
            var temp2 = Expr.Ident(v2);
            var temp1 = new OldExpr(Token.NoToken, Expr.Ident(v1));
            return new AssumeCmd(Token.NoToken, Expr.Le(temp1, temp2));

        }

        // var1 == const
        public static AssumeCmd MkAssumeVarEqConst(Variable v, int c)
        {
            Expr temp1 = Expr.Ident(v);
            Expr temp2 = Expr.Literal(c);
            return new AssumeCmd(Token.NoToken, Expr.Eq(temp1, temp2));
        }

        // var1 == const
        public static AssumeCmd MkAssumeVarEqConst(Variable v, bool c)
        {
            Expr temp1 = Expr.Ident(v);
            if (c)
            {
                return new AssumeCmd(Token.NoToken, temp1);
            }
            else
            {
                return new AssumeCmd(Token.NoToken, Expr.Not(temp1));
            }

        }

        public static AssumeCmd MkAssumeVarLeVar(Variable v1, Variable v2)
        {
            Expr temp1 = Expr.Ident(v1);
            Expr temp2 = Expr.Ident(v2);
            return new AssumeCmd(Token.NoToken, Expr.Le(temp1, temp2));
        }

        // var1 == var2
        public static AssumeCmd MkAssumeVarEqVar(Variable v1, Variable v2)
        {
            Expr temp1 = Expr.Ident(v1);
            Expr temp2 = Expr.Ident(v2);
            return new AssumeCmd(Token.NoToken, Expr.Eq(temp1, temp2));
        }

        // var1 == var2
        public static Expr MkExprVarEqVar(Variable v1, Variable v2)
        {
            return MkAssumeVarEqVar(v1, v2).Expr;
        }

        // var1 == const
        public static AssertCmd MkAssertVarEqConst(Variable v, bool c)
        {
            Expr temp1 = Expr.Ident(v);
            Expr temp2 = Expr.Literal(c);
            return new AssertCmd(Token.NoToken, Expr.Eq(temp1, temp2));
        }

        // havoc v
        public static HavocCmd MkHavocVar(Variable v)
        {
            List<IdentifierExpr> tmp = new List<IdentifierExpr>();
            tmp.Add(Expr.Ident(v));
            return new HavocCmd(Token.NoToken, tmp);
        }

        //assume(inAtomicBlock => (old(k) == k && not(raiseException)))
        public static AssumeCmd MkAssumeInAtomic(Variable inAtomicBlock, Variable k, Variable raiseException)
        {
            Expr tempA = Expr.Ident(inAtomicBlock);
            Expr tempK = Expr.Ident(k);
            Expr tempOK = new OldExpr(Token.NoToken, Expr.Ident(k));
            Expr tempR = Expr.Ident(raiseException);

            Expr e1 = Expr.Eq(tempK, tempOK);
            Expr e2 = Expr.Not(tempR);
            Expr e3 = Expr.And(e1, e2);
            Expr e4 = Expr.Imp(tempA, e3);

            return new AssumeCmd(Token.NoToken, e4);
        }

        // goto lbl
        public static GotoCmd MkGotoCmd(string lab)
        {
            List<String> ss = new List<String>();
            ss.Add(lab);
            return new GotoCmd(Token.NoToken, ss);
        }

        // goto lab1, lab2
        public static GotoCmd MkGotoCmd(string lab1, string lab2)
        {
            List<String> ss = new List<String>();
            ss.Add(lab1);
            ss.Add(lab2);
            return new GotoCmd(Token.NoToken, ss);
        }

        // assume (forall x:int :: map[x] == v)
        public static AssumeCmd MkMapConstant(Variable map, bool v)
        {
            BoundVariable x = new BoundVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Int));

            List<Variable> vs = new List<Variable>();
            vs.Add(x);

            List<Expr> args = new List<Expr>();
            args.Add(Expr.Ident(x));

            Expr cond = new ForallExpr(Token.NoToken, vs,
                Expr.Eq(Expr.Select(Expr.Ident(map), args), Expr.Literal(v)));

            return new AssumeCmd(Token.NoToken, cond);
        }

        // assume (forall x:int :: map[x] == v)
        public static AssumeCmd MkMapConstant(Variable map, int v)
        {
            BoundVariable x = new BoundVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Int));

            List<Variable> vs = new List<Variable>();
            vs.Add(x);

            List<Expr> args = new List<Expr>();
            args.Add(Expr.Ident(x));

            Expr cond = new ForallExpr(Token.NoToken, vs,
                Expr.Eq(Expr.Select(Expr.Ident(map), args), Expr.Literal(v)));

            return new AssumeCmd(Token.NoToken, cond);
        }

        // assume (forall x:int :: (x != v1) => map[x])
        public static AssumeCmd MkJoinAllCmd1(Variable map, Variable v1)
        {
            BoundVariable x = new BoundVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Int));

            List<Variable> vs = new List<Variable>();
            vs.Add(x);

            List<Expr> args = new List<Expr>();
            args.Add(Expr.Ident(x));

            Expr cond = new ForallExpr(Token.NoToken, vs,
                Expr.Imp(Expr.Neq(Expr.Ident(x), Expr.Ident(v1)),
                         Expr.Select(Expr.Ident(map), args)));

            return new AssumeCmd(Token.NoToken, cond);
        }

        // assume (forall x:int :: (x != v1) => map[x] <= v2)
        public static AssumeCmd MkJoinAllCmd2(Variable map, Variable v1, Variable v2)
        {
            BoundVariable x = new BoundVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, "x", Microsoft.Boogie.Type.Int));

            List<Variable> vs = new List<Variable>();
            vs.Add(x);

            List<Expr> args = new List<Expr>();
            args.Add(Expr.Ident(x));

            Expr cond = new ForallExpr(Token.NoToken, vs,
                Expr.Imp(Expr.Neq(Expr.Ident(x), Expr.Ident(v1)),
                         Expr.Le(Expr.Select(Expr.Ident(map), args), Expr.Ident(v2))));

            return new AssumeCmd(Token.NoToken, cond);
        }




        // map[v] := rhs
        public static AssignCmd MkMapAssign(Variable map, Expr v, Expr rhs)
        {
            AssignLhs alhs = new SimpleAssignLhs(Token.NoToken,
                new IdentifierExpr(Token.NoToken, map));

            var indices = new List<Expr>();
            indices.Add(v);

            MapAssignLhs lhs = new MapAssignLhs(Token.NoToken, alhs, indices);

            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();

            lhss.Add(lhs);
            rhss.Add(rhs);

            return new AssignCmd(Token.NoToken, lhss, rhss);
        }

        // map[v] 
        public static Expr MkMapAccessExpr(Variable map, Expr v)
        {
            var indices = new List<Expr>();
            indices.Add(v);

            return Expr.Select(Expr.Ident(map), indices);
        }

        // Factory methods added by mje -- I hope these are non redundant.

        public static Microsoft.Boogie.Type MkMapType(
            Microsoft.Boogie.Type src, Microsoft.Boogie.Type dest)
        {
            return new MapType(Token.NoToken, new List<TypeVariable>(),
                new List<Microsoft.Boogie.Type>(new Microsoft.Boogie.Type[] { src }), dest);
        }

        public static Declaration MkProc(string name, List<Variable> ins, List<Variable> outs)
        {
            return new Procedure(
                Token.NoToken, name, new List<TypeVariable>(), ins, outs,
                false, new List<Requires>(), new List<Requires>(), new List<Ensures>(),
                new List<IdentifierExpr>());
        }
        public static Declaration MkProc(string name,
            IEnumerable<Variable> ins, IEnumerable<Variable> outs)
        {
            return MkProc(name,
                new List<Variable>(ins.ToArray()),
                new List<Variable>(outs.ToArray()));
        }

        public static List<Declaration> MkImpl(string name, List<Variable> ins, List<Variable> outs,
            List<Variable> locals, IEnumerable<Block> blocks)
        {
            var pr = MkProc(name, ins, outs);
            var im = new Implementation(
                Token.NoToken, name, new List<TypeVariable>(),
                ins, outs, locals, new List<Block>(blocks));
            im.Proc = pr as Procedure;
            return new List<Declaration>(new Declaration[] { pr, im });
        }

        //public static Implementation MkImpl(Procedure proc, List<Variable> ins, List<Variable> outs,
        //    List<Variable> locals, IEnumerable<Block> blocks)
        //{
        //    var im = new Implementation(
        //        Token.NoToken, proc.Name, new List<TypeVariable>(),
        //        ins, outs, locals, new List<Block>(blocks));
        //    im.Proc = proc;
        //    return im;
        //}

        public static List<Declaration> MkImpl(string name, List<Variable> ins, List<Variable> outs,
            List<Variable> locals, IEnumerable<Cmd> cs)
        {
            return MkImpl(name, ins, outs, locals, new Block[] { MkBlock(cs) });
        }

        public static Variable MkGlobal(string name, Microsoft.Boogie.Type t)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, t));
        }

        public static Variable MkLocal(string name, Microsoft.Boogie.Type t)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, t));
        }

        public static Variable MkFormal(string name, Microsoft.Boogie.Type t, bool incoming)
        {
            return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, name, t), incoming);
        }

        public static Variable MkVarCopy(string name, Variable v)
        {
            if (v is GlobalVariable)
                return MkGlobal(name, v.TypedIdent.Type);
            if (v is LocalVariable)
                return MkLocal(name, v.TypedIdent.Type);
            if (v is Formal)
                return MkFormal(name, v.TypedIdent.Type, (v as Formal).InComing);
            if (v is Constant)
                return new Constant(Token.NoToken, new TypedIdent(Token.NoToken,
                    name, v.TypedIdent.Type));
            Debug.Assert(false);
            return null;
        }

        public static Expr MkEqual(Variable v, int n)
        {
            return Expr.Eq(Expr.Ident(v), Expr.Literal(n));
        }

        public static Expr MkConj(List<Expr> es)
        {
            if (es.Count < 1) return Expr.True;
            else
            {
                var e = es[0];
                es.RemoveAt(0);
                foreach (var f in es)
                    e = Expr.And(e, f);
                return e;
            }
        }

        public static Cmd MkAssume(Expr e)
        {
            return new AssumeCmd(Token.NoToken, e);
        }

        public static AssertCmd MkAssert(Expr e)
        {
            return new AssertCmd(Token.NoToken, e);
        }

        /**
         * Assignment constructors.
         **/
        public static Cmd MkAssign(Variable v, Expr e)
        {
            var lhs = new List<AssignLhs>();
            var rhs = new List<Expr>();
            lhs.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(v)));
            rhs.Add(e);
            return new AssignCmd(Token.NoToken, lhs, rhs);
        }
        public static Cmd MkAssign(Variable v, Variable w)
        {
            return MkAssign(v, Expr.Ident(w));
        }
        public static Cmd MkAssign(Variable v, bool b)
        {
            return MkAssign(v, Expr.Literal(b));
        }
        public static Cmd MkAssign(Variable v, int i)
        {
            return MkAssign(v, Expr.Literal(i));
        }

        /**
         * Call constructors.
         **/
        public static Cmd MkCall(string proc, IEnumerable<Expr> args, IEnumerable<Variable> rets)
        {
            return new CallCmd(Token.NoToken, proc, new List<Expr>(args),
                new List<Variable>(rets).Map<Variable, IdentifierExpr>(v =>
                    Expr.Ident(v.Name, v.TypedIdent.Type)),
                null);
        }
        public static Cmd MkCall(Procedure p, IEnumerable<Expr> args, IEnumerable<Variable> rets)
        {
            return MkCall(p.Name, args, rets);
        }
        public static Cmd MkAsync(int level, string proc, IEnumerable<Expr> args)
        {
            var vs = new List<object>();
            if (level >= 0)
            {
                vs.Add(Expr.Literal(level));
            }
            else vs.Add("same");

            var attrs = new QKeyValue(Token.NoToken, "level", vs, null);
            var ret = new CallCmd(Token.NoToken, proc, new List<Expr>(args),
                new List<IdentifierExpr>(), attrs);
            ret.IsAsync = true;

            return ret;
        }

        /**
         * Block constructors.
         */
        public static Block MkBlock(List<Cmd> cs, TransferCmd tx)
        {
            return new Block(Token.NoToken, uniqueLabel(), cs, tx);
        }
        public static Block MkBlock(IEnumerable<Cmd> cs, IEnumerable<String> tx)
        {
            return MkBlock(
                new List<Cmd>(cs.ToArray()),
                new GotoCmd(Token.NoToken, new List<String>(tx.ToArray())));
        }
        public static Block MkBlock(List<Cmd> cs)
        {
            return MkBlock(cs, new ReturnCmd(Token.NoToken));
        }
        public static Block MkBlock(IEnumerable<Cmd> cs)
        {
            return MkBlock(new List<Cmd>(cs.ToArray()));
        }
        public static Block MkBlock(Cmd c)
        {
            return MkBlock(new Cmd[] { c });
        }
        public static Block MkBlock()
        {
            return MkBlock(new List<Cmd>());
        }

        /*
         * Clone a block
         */
        public static Block CloneBlock(Block blk)
        {
            return new Block(
                CloneToken(blk.tok),
                blk.Label.Clone() as string,
                CloneCmdSeq(blk.Cmds),
                CloneTransferCmd(blk.TransferCmd));
        }

        public static List<Cmd> CloneCmdSeq(List<Cmd> cmdseq)
        {
            List<Cmd> result = new List<Cmd>(cmdseq);
            return result;
        }
        public static TransferCmd CloneTransferCmd(TransferCmd cmd)
        {
            if (cmd is GotoCmd)
                return CloneGotoCmd(cmd as GotoCmd);
            else if (cmd is ReturnCmd)
                return CloneReturnCmd(cmd as ReturnCmd);
            else
                return null;
        }
        public static GotoCmd CloneGotoCmd(GotoCmd cmd)
        {
            return new GotoCmd(CloneToken(cmd.tok), CloneStringSeq(cmd.LabelNames));
        }
        public static ReturnCmd CloneReturnCmd(ReturnCmd cmd)
        {
            return new ReturnCmd(CloneToken(cmd.tok));
        }

        public static List<String> CloneStringSeq(List<String> seq)
        {
            List<String> result = new List<String>();
            foreach (string str in seq)
                result.Add(str.Clone() as String);
            return result;
        }
        public static Token CloneToken(Token tok)
        {
            return new Token(tok.line, tok.col);
        }
        public static IToken CloneToken(IToken tok)
        {
            if (tok == Token.NoToken)
                return Token.NoToken;
            else
                return CloneToken(tok as Token);
        }


        /**
         * Block sequencing.
         * Connects the last block of the first enumeration to the first block of the second.
         **/
        public static void Sequence(IEnumerable<Block> bs, IEnumerable<Block> cs)
        {
            if (bs.Count() < 1 || cs.Count() < 1) return;

            bs.Last().TransferCmd =
                new GotoCmd(Token.NoToken,
                    new List<String>(new String[] { cs.First().Label }));
        }

        /**
         * MkNondetSwitch( cmds1, cmds2, .., cmdsN )
         * 
         * A non-deterministic switch statement.
         * 
         * goto L1, L2, .., Ln;
         * L1: cmds1; goto L;
         * L2: cmds2; goto L;
         * ..
         * Ln: cmdsN; goto L;
         * L: skip;
         * 
         **/
        public static List<Block> MkNondetSwitch(IEnumerable<IEnumerable<Cmd>> css)
        {
            var tail = MkBlock();
            var ls = new List<String>();

            var ds = new List<Block>();
            foreach (var cs in css)
            {
                var b = MkBlock(cs, new String[] { tail.Label });
                ls.Add(b.Label);
                ds.Add(b);
            }

            var head = MkBlock(new Cmd[] { }, ls);

            var bs = new List<Block>();
            bs.Add(head);
            bs.AddRange(ds);
            bs.Add(tail);
            return bs;
        }


        private static List<String> extractVars(Cmd cmd, bool getLhs, bool getRhs)
        {
            if (cmd is AssertCmd)
                return extractVars((cmd as AssertCmd).Expr);
            if (cmd is AssumeCmd)
                return extractVars((cmd as AssumeCmd).Expr);
            if (cmd is HavocCmd)
            {
                List<String> ret = new List<string>();
                foreach (IdentifierExpr v in (cmd as HavocCmd).Vars)
                {
                    ret.Add(v.Decl.Name);
                }
                return ret;
            }
            else if (cmd is CallCmd)
            {
                List<String> ret = new List<string>();
                CallCmd ccmd = cmd as CallCmd;
                if (getRhs)
                {
                    foreach (IdentifierExpr v in ccmd.Outs)
                    {
                        if (v != null) ret.Add(v.Decl.Name);
                    }
                }
                return ret;
            }
            else if (cmd is AssignCmd)
            {
                List<String> ret = new List<string>();
                var acmd = cmd as AssignCmd;
                if (getLhs)
                {
                    foreach (var ae in acmd.Lhss)
                    {
                        var v = ae.DeepAssignedVariable;
                        ret.Add(v.Name);
                    }
                }
                if (getRhs)
                {
                    foreach (var ae in acmd.Rhss)
                    {
                        ret.AddRange(extractVars(ae));
                    }
                }
                return ret;
            }

            throw new NotImplementedException("call cmd in extractvars nnot handled");

        }

        public static List<String> extractVars(Expr expr)
        {
            List<string> ret = new List<string>();
            if (expr is IdentifierExpr)
            {
                IdentifierExpr iexpr = expr as IdentifierExpr;
                ret.Add(iexpr.Decl.Name);
                return ret;
            }
            else if (expr is LiteralExpr)
            {
                return ret;
            }
            else if (expr is NAryExpr)
            {
                NAryExpr nexpr = expr as NAryExpr;
                for (int i = 0; i < nexpr.Args.Count; i++)
                {
                    ret.AddRange(extractVars(nexpr.Args[i]));
                }
                return ret;
            }
            throw new NotImplementedException(expr.ToString());
        }

        public static List<String> extractRHSVars(Cmd wcmd)
        {
            return extractVars(wcmd, false, true);
        }
        public static List<String> extractLHSVars(Cmd wcmd)
        {
            return extractVars(wcmd, true, false);
        }
        public static List<String> extractVars(Cmd cmd)
        {
            return extractVars(cmd, true, true);
        }
    }

}

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using cba;
using cba.Util;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;

namespace CoreLib
{
    /// <summary>
    /// Experimental, opt-in outlining of large single-entry dispatcher arms.
    /// This deliberately recognizes only a narrow reducible-loop shape.  It
    /// moves the exact commands into ordinary Boogie implementations; it never
    /// replaces state with havoc or a summary.
    /// </summary>
    public static class DispatcherOutlining
    {
        public enum Mode
        {
            Disabled,
            DispatcherArms,
            WeightedGroups
        }

        public sealed class Result
        {
            public Mode OutlineMode;
            public int Regions;
            public int SyntheticProcedures;
            public int OriginalBlocks;
            public int CallerBlocksAfter;
            public bool Changed => SyntheticProcedures != 0;
            internal readonly Dictionary<string, TraceMapping> traceMappings =
                new Dictionary<string, TraceMapping>();

            public ErrorTrace MapBackTrace(ErrorTrace trace)
            {
                return trace == null ? null : MapOrdinaryTrace(trace);
            }

            private ErrorTrace MapOrdinaryTrace(ErrorTrace trace)
            {
                var mapped = new ErrorTrace(trace.procName);
                foreach (var block in trace.Blocks)
                {
                    if (block.blockName.StartsWith("$outline_exit_dispatch$", StringComparison.Ordinal))
                        continue;
                    var syntheticCall = block.Cmds.OfType<CallInstr>()
                        .FirstOrDefault(call => traceMappings.ContainsKey(call.callee));
                    if (syntheticCall != null)
                    {
                        if (syntheticCall.calleeTrace == null)
                            throw new InternalError("An outlined call on a concrete error trace was not expanded");
                        foreach (var flattened in FlattenSynthetic(syntheticCall.calleeTrace,
                                     traceMappings[syntheticCall.callee]))
                            mapped.addBlock(flattened);
                        continue;
                    }
                    mapped.addBlock(MapBlock(block));
                }
                if (trace.returns)
                    mapped.addReturn(trace.raisesException);
                return mapped;
            }

            private IEnumerable<ErrorTraceBlock> FlattenSynthetic(ErrorTrace trace, TraceMapping mapping)
            {
                foreach (var block in trace.Blocks)
                {
                    if (!mapping.BlockLabels.TryGetValue(block.blockName, out var originalLabel))
                        continue;
                    var mapped = MapBlock(block, originalLabel);
                    yield return mapped;
                }
            }

            private ErrorTraceBlock MapBlock(ErrorTraceBlock block, string label = null)
            {
                var mapped = new ErrorTraceBlock(label ?? block.blockName);
                if (block.info != null)
                    mapped.info = block.info.Copy();
                foreach (var instruction in block.Cmds)
                {
                    if (instruction is CallInstr call && call.calleeTrace != null)
                    {
                        if (traceMappings.TryGetValue(call.callee, out var synthetic))
                        {
                            // Nested outlined calls are not expected in the narrow
                            // dispatcher shape.  Preserve correctness by rejecting
                            // such a trace instead of silently retaining a helper.
                            throw new InternalError("Nested dispatcher outlines are not supported in trace mapping: " +
                                synthetic.Caller);
                        }
                        mapped.addInstr(new CallInstr(call.callee, MapOrdinaryTrace(call.calleeTrace),
                            call.asyncCall, call.info?.Copy()));
                    }
                    else
                    {
                        mapped.addInstr(instruction.Copy());
                    }
                }
                return mapped;
            }
        }

        internal sealed class TraceMapping
        {
            public string Caller;
            public readonly Dictionary<string, string> BlockLabels = new Dictionary<string, string>();
        }

        private sealed class Region
        {
            public Implementation Implementation;
            public Block Header;
            public Block Root;
            public List<Block> Continuations;
            public HashSet<Block> Blocks;
            public int CommandCount;
            public int CallCount;
            public HashSet<Variable> LiveIns;
            public HashSet<Variable> LiveOuts;
            public int Weight => CommandCount + 8 * CallCount;
        }

        private sealed class Group
        {
            public readonly List<Region> Regions = new List<Region>();
            public int Weight;
        }

        private static int syntheticCounter;
        private static int dumpCounter;

        public static Mode ConfiguredMode
        {
            get
            {
                var value = Environment.GetEnvironmentVariable("CORRAL_SI_OUTLINE");
                if (string.Equals(value, "dispatcher-arms", StringComparison.OrdinalIgnoreCase))
                    return Mode.DispatcherArms;
                if (string.Equals(value, "weighted-groups", StringComparison.OrdinalIgnoreCase))
                    return Mode.WeightedGroups;
                return Mode.Disabled;
            }
        }

        public static Result Apply(Program program)
        {
            var mode = ConfiguredMode;
            var dumpId = dumpCounter++;
            DumpProgram(program, dumpId, "before");
            var result = new Result
            {
                OutlineMode = mode,
                OriginalBlocks = program.Implementations.Sum(impl => impl.Blocks.Count)
            };
            if (mode == Mode.Disabled)
            {
                result.CallerBlocksAfter = result.OriginalBlocks;
                return result;
            }

            var minimumFanout = ReadInt("CORRAL_SI_OUTLINE_MIN_FANOUT", 16, 2);
            var minimumBlocks = ReadInt("CORRAL_SI_OUTLINE_MIN_BLOCKS", 4, 1);
            var minimumCommands = ReadInt("CORRAL_SI_OUTLINE_MIN_CMDS", 24, 1);
            var maximumExits = ReadInt("CORRAL_SI_OUTLINE_MAX_EXITS", 3, 1);
            var targetGroups = ReadInt("CORRAL_SI_OUTLINE_GROUPS", 12, 1);
            var declarations = new List<Declaration>();
            var removedBlocks = 0;
            var existingNames = new HashSet<string>(program.TopLevelDeclarations
                .OfType<NamedDeclaration>().Select(decl => decl.Name));
            var nextCallId = NextCallId(program);

            foreach (var implementation in program.Implementations.ToList())
            {
                if (implementation.Blocks.Count == 0 || implementation.TypeParameters.Count != 0)
                    continue;

                var candidates = FindRegions(implementation, minimumBlocks, minimumCommands,
                    maximumExits);
                var selected = new List<Region>();
                var occupied = new HashSet<Block>();
                foreach (var region in candidates.OrderByDescending(candidate => candidate.Weight))
                {
                    if (region.Blocks.Overlaps(occupied))
                        continue;
                    selected.Add(region);
                    occupied.UnionWith(region.Blocks);
                }
                if (selected.Count < minimumFanout)
                    continue;

                // The candidates are discovered structurally, but their helper
                // interfaces must reflect data flow through the original cyclic
                // implementation.  Compute a genuine loop fixed point before
                // mutating any blocks.  This keeps internal temporaries inside
                // the helper instead of threading every touched caller local
                // through every outlined call.
                var liveBefore = ComputeLiveVariables(implementation);
                foreach (var region in selected)
                {
                    region.LiveIns = new HashSet<Variable>(liveBefore[region.Root]);
                    region.LiveOuts = new HashSet<Variable>();
                    foreach (var continuation in region.Continuations)
                        region.LiveOuts.UnionWith(liveBefore[continuation]);
                }

                IEnumerable<Group> groups;
                if (mode == Mode.DispatcherArms)
                {
                    groups = selected.Select(region =>
                    {
                        var group = new Group();
                        group.Regions.Add(region);
                        group.Weight = region.Weight;
                        return group;
                    }).ToList();
                }
                else
                {
                    groups = MakeWeightedGroups(selected, targetGroups);
                }

                var removed = new HashSet<Block>();
                foreach (var group in groups)
                {
                    if (group.Regions.Count == 0)
                        continue;
                    var helperName = FreshName(existingNames, implementation.Name);
                    var helper = BuildHelper(implementation, group.Regions, helperName, ref nextCallId,
                        result.traceMappings);
                    declarations.Add(helper.Item1);
                    declarations.Add(helper.Item2);
                    result.SyntheticProcedures++;

                    foreach (var region in group.Regions)
                    {
                        result.Regions++;
                        foreach (var block in region.Blocks)
                        {
                            if (block != region.Root)
                                removed.Add(block);
                        }
                        SiProfile.Write("OUTLINE_REGION",
                            ("implementation", implementation.Name),
                            ("outline_mode", ModeName(mode)),
                            ("callee", helperName),
                            ("region_blocks", SiProfile.Number(region.Blocks.Count)),
                            ("region_cmds", SiProfile.Number(region.CommandCount)),
                            ("region_calls", SiProfile.Number(region.CallCount)),
                            ("details", "header=" + region.Header.Label + ";entry=" + region.Root.Label +
                                ";continuations=" + string.Join(",", region.Continuations.Select(block => block.Label)) +
                                ";group_size=" + group.Regions.Count));
                    }
                }
                for (var index = implementation.Blocks.Count - 1; index >= 0; index--)
                {
                    if (removed.Contains(implementation.Blocks[index]))
                    {
                        implementation.Blocks.RemoveAt(index);
                        removedBlocks++;
                    }
                }
            }

            foreach (var declaration in declarations)
                program.AddTopLevelDeclaration(declaration);
            result.CallerBlocksAfter = result.OriginalBlocks - removedBlocks;
            SiProfile.Write("OUTLINE_SUMMARY",
                ("outline_mode", ModeName(mode)),
                ("outlined_regions", SiProfile.Number(result.Regions)),
                ("synthetic_procs", SiProfile.Number(result.SyntheticProcedures)),
                ("original_blocks", SiProfile.Number(result.OriginalBlocks)),
                ("caller_blocks_after", SiProfile.Number(result.CallerBlocksAfter)),
                ("details", "min_fanout=" + minimumFanout + ";min_blocks=" + minimumBlocks +
                    ";min_cmds=" + minimumCommands + ";max_exits=" + maximumExits +
                    ";target_groups=" + targetGroups));
            DumpProgram(program, dumpId, "outlined");
            return result;
        }

        private static void DumpProgram(Program program, int id, string stage)
        {
            var directory = Environment.GetEnvironmentVariable("CORRAL_SI_OUTLINE_DUMP");
            if (ConfiguredMode == Mode.Disabled || string.IsNullOrWhiteSpace(directory))
                return;
            Directory.CreateDirectory(directory);
            BoogieUtil.PrintProgram(program, Path.Combine(directory,
                "outline-" + id.ToString("D3") + "-" + stage + ".bpl"));
        }

        private static List<Region> FindRegions(Implementation implementation, int minimumBlocks,
            int minimumCommands, int maximumExits)
        {
            var graph = Program.GraphFromImpl(implementation);
            // Some earlier Corral passes retain unreachable connected components.
            // Boogie's dominator implementation assumes every node is reachable
            // from Graph.Source, so analyze an entry-reachable view rather than
            // pruning (and therefore mutating) the caller as a side effect here.
            var reachable = graph.Reachable();
            if (reachable.Count != graph.Nodes.Count)
                graph = Program.GraphFromBlocksSubset(implementation.Blocks,
                    new HashSet<Block>(reachable));
            graph.ComputeLoops();
            if (!graph.Reducible)
                return new List<Region>();

            var regions = new List<Region>();
            foreach (var header in graph.Headers)
            {
                var rejectedTransfer = 0;
                var rejectedEntry = 0;
                var rejectedExit = 0;
                var rejectedCycle = 0;
                var rejectedSmall = 0;
                var rejectedWhere = 0;
                var accepted = 0;
                var loopBlocks = new HashSet<Block>();
                foreach (var backEdge in graph.BackEdgeNodes(header))
                    loopBlocks.UnionWith(graph.NaturalLoops(header, backEdge));
                if (loopBlocks.Count == 0)
                    continue;

                // Do not use the first payload call as the boundary: assertion
                // splitting often puts that call near the bottom of the arm.  A
                // complete dispatcher arm is instead the largest dominated,
                // single-entry subregion with a small explicit exit set.
                var roots = new HashSet<Block>(loopBlocks.Where(block => block != header));
                foreach (var root in roots)
                {
                    var blocks = new HashSet<Block>(loopBlocks.Where(block => block != header &&
                        graph.DominatorMap.DominatedBy(block, root)));
                    if (!blocks.Contains(root) || blocks.Count < minimumBlocks)
                    {
                        rejectedSmall++;
                        continue;
                    }
                    if (blocks.Any(block => block.TransferCmd is not GotoCmd))
                    {
                        rejectedTransfer++;
                        continue;
                    }
                    var hasSideEntry = blocks.Any(block => block != root &&
                        graph.Predecessors(block).Any(predecessor => !blocks.Contains(predecessor)));
                    if (hasSideEntry)
                    {
                        rejectedEntry++;
                        continue;
                    }
                    var outsideTargets = blocks.SelectMany(block => graph.Successors(block))
                        .Where(successor => !blocks.Contains(successor)).Distinct().ToList();
                    if (outsideTargets.Count == 0 || outsideTargets.Count > maximumExits)
                    {
                        rejectedExit++;
                        continue;
                    }
                    if (!IsAcyclic(blocks, graph))
                    {
                        rejectedCycle++;
                        continue;
                    }
                    var commands = blocks.Sum(block => block.Cmds.Count);
                    if (commands < minimumCommands)
                    {
                        rejectedSmall++;
                        continue;
                    }
                    var variables = VariableCollector.Collect(blocks.SelectMany(block => block.Cmds)).ToList();
                    if (variables.Any(variable => variable.TypedIdent.WhereExpr != null))
                    {
                        rejectedWhere++;
                        continue;
                    }
                    accepted++;
                    regions.Add(new Region
                    {
                        Implementation = implementation,
                        Header = header,
                        Root = root,
                        Continuations = outsideTargets,
                        Blocks = blocks,
                        CommandCount = commands,
                        CallCount = blocks.Sum(block => block.Cmds.OfType<CallCmd>().Count())
                    });
                }
                SiProfile.Write("OUTLINE_LOOP_SCAN",
                    ("implementation", implementation.Name),
                    ("outline_mode", ModeName(ConfiguredMode)),
                    ("count", SiProfile.Number(accepted)),
                    ("open_calls", SiProfile.Number(roots.Count)),
                    ("region_blocks", SiProfile.Number(loopBlocks.Count)),
                    ("top_callees", ""),
                    ("details", "header=" + header.Label + ";roots=" + roots.Count +
                        ";accepted=" + accepted + ";small=" + rejectedSmall +
                        ";transfer=" + rejectedTransfer + ";entry=" + rejectedEntry +
                        ";exit=" + rejectedExit + ";cycle=" + rejectedCycle +
                        ";where=" + rejectedWhere));
            }
            return regions;
        }

        private static bool IsAcyclic(HashSet<Block> blocks, Graph<Block> graph)
        {
            var indegree = blocks.ToDictionary(block => block,
                block => graph.Predecessors(block).Count(blocks.Contains));
            var work = new Queue<Block>(indegree.Where(pair => pair.Value == 0).Select(pair => pair.Key));
            var seen = 0;
            while (work.Count > 0)
            {
                var block = work.Dequeue();
                seen++;
                foreach (var successor in graph.Successors(block).Where(blocks.Contains))
                {
                    indegree[successor]--;
                    if (indegree[successor] == 0)
                        work.Enqueue(successor);
                }
            }
            return seen == blocks.Count;
        }

        private static List<Group> MakeWeightedGroups(List<Region> regions, int targetGroups)
        {
            var groups = new List<Group>();
            var number = Math.Min(targetGroups, regions.Count);
            var bins = Enumerable.Range(0, number).Select(_ => new Group()).ToList();
            foreach (var region in regions.OrderByDescending(item => item.Weight))
            {
                var bin = bins.OrderBy(item => item.Weight).First();
                bin.Regions.Add(region);
                bin.Weight += region.Weight;
            }
            groups.AddRange(bins);
            return groups;
        }

        /// <summary>
        /// Backward may-liveness on the entry-reachable CFG.  Boogie's stock
        /// LiveVariableAnalysis is intentionally driven by a topological order;
        /// at this pipeline point loops have not been extracted yet, so use a
        /// predecessor worklist to compute the cyclic fixed point directly.
        /// </summary>
        private static Dictionary<Block, HashSet<Variable>> ComputeLiveVariables(
            Implementation implementation)
        {
            var graph = Program.GraphFromImpl(implementation);
            var reachable = new HashSet<Block>(graph.Reachable());
            var liveBefore = reachable.ToDictionary(block => block,
                block => new HashSet<Variable>());
            var work = new Queue<Block>(reachable);
            var queued = new HashSet<Block>(reachable);

            while (work.Count > 0)
            {
                var block = work.Dequeue();
                queued.Remove(block);
                var live = new HashSet<Variable>();
                foreach (var successor in graph.Successors(block))
                {
                    if (liveBefore.TryGetValue(successor, out var successorLive))
                        live.UnionWith(successorLive);
                }
                if (block.TransferCmd is ReturnCmd)
                    live.UnionWith(implementation.OutParams);
                for (var index = block.Cmds.Count - 1; index >= 0; index--)
                    PropagateLiveness(block.Cmds[index], live);

                if (live.SetEquals(liveBefore[block]))
                    continue;
                liveBefore[block] = live;
                foreach (var predecessor in graph.Predecessors(block))
                {
                    if (reachable.Contains(predecessor) && queued.Add(predecessor))
                        work.Enqueue(predecessor);
                }
            }
            return liveBefore;
        }

        private static void PropagateLiveness(Cmd command, HashSet<Variable> live)
        {
            if (command is AssignCmd assign)
            {
                var simple = assign.AsSimpleAssignCmd;
                var usedRightHandSides = new HashSet<int>();
                for (var index = 0; index < simple.Lhss.Count; index++)
                {
                    var variable = simple.Lhss[index].DeepAssignedVariable;
                    // A global write is externally observable even when no
                    // later command in this implementation reads the global.
                    if (variable is GlobalVariable || variable != null && live.Remove(variable))
                        usedRightHandSides.Add(index);
                }
                foreach (var index in usedRightHandSides)
                    live.UnionWith(VariableCollector.Collect(simple.Rhss[index]));
                return;
            }
            if (command is HavocCmd havoc)
            {
                foreach (var variable in havoc.Vars.Select(expr => expr.Decl)
                             .Where(variable => variable is not GlobalVariable))
                    live.Remove(variable);
                return;
            }
            if (command is PredicateCmd predicate)
            {
                if (predicate.Expr is LiteralExpr literal && literal.IsFalse)
                    live.Clear();
                else
                    live.UnionWith(VariableCollector.Collect(predicate.Expr));
                return;
            }
            if (command is CallCmd call)
            {
                foreach (var output in call.Outs)
                {
                    if (output.Decl is not GlobalVariable)
                        live.Remove(output.Decl);
                }
                // Inputs may occur in requires clauses or control a global
                // side effect even when no returned local is live.
                live.UnionWith(VariableCollector.Collect(call.Ins));
                return;
            }
            if (command is SugaredCmd sugared)
            {
                PropagateLiveness(sugared.GetDesugaring(BoogieUtil.BoogieOptions), live);
                return;
            }
            if (command is StateCmd state)
            {
                for (var index = state.Cmds.Count - 1; index >= 0; index--)
                    PropagateLiveness(state.Cmds[index], live);
                live.ExceptWith(state.Locals);
                return;
            }
            if (command is CommentCmd || command is HideRevealCmd || command is ChangeScope)
                return;

            // Unknown future command kinds remain conservative: every variable
            // mentioned is treated as a use and no variable is killed.
            live.UnionWith(VariableCollector.Collect(command));
        }

        private static Tuple<Procedure, Implementation> BuildHelper(Implementation caller,
            List<Region> regions, string name, ref int nextCallId,
            Dictionary<string, TraceMapping> traceMappings)
        {
            var traceMapping = new TraceMapping { Caller = caller.Name };
            traceMappings.Add(name, traceMapping);
            var allBlocks = new HashSet<Block>(regions.SelectMany(region => region.Blocks));
            var footprint = new HashSet<Variable>(VariableCollector.Collect(
                allBlocks.SelectMany(block => block.Cmds)));
            var targets = new HashSet<Variable>(allBlocks.SelectMany(block => block.Cmds)
                .SelectMany(command => command.GetAssignedVariables()));
            var callerVariables = caller.InParams.Concat(caller.OutParams).Concat(caller.LocVars).ToList();
            var callerVariableSet = new HashSet<Variable>(callerVariables);
            var liveInputs = new HashSet<Variable>(regions.SelectMany(region => region.LiveIns));
            var liveOutputs = new HashSet<Variable>(regions.SelectMany(region => region.LiveOuts));
            liveInputs.IntersectWith(callerVariableSet);
            liveOutputs.IntersectWith(callerVariableSet);
            liveOutputs.IntersectWith(targets);

            // A grouped helper has one union output signature.  An arm that
            // does not define another arm's output must preserve its incoming
            // value, so every grouped output is also an input.  A one-arm
            // helper needs only the actual fixed-point live-ins.
            if (regions.Count > 1)
                liveInputs.UnionWith(liveOutputs);
            var stateVariables = callerVariables.Where(liveInputs.Contains).ToList();
            var outputVariables = callerVariables.Where(liveOutputs.Contains).ToList();

            var inputs = new List<Variable>();
            Formal selector = null;
            if (regions.Count > 1)
            {
                selector = new Formal(Token.NoToken,
                    new TypedIdent(Token.NoToken, "$arm", Microsoft.Boogie.Type.Int), true);
                inputs.Add(selector);
            }
            var inputByOriginal = new Dictionary<Variable, Formal>();
            foreach (var variable in stateVariables)
            {
                var formal = new Formal(variable.tok,
                    new TypedIdent(variable.TypedIdent.tok, "in_" + variable.Name,
                        variable.TypedIdent.Type), true);
                inputs.Add(formal);
                inputByOriginal.Add(variable, formal);
            }
            var outputs = new List<Variable>();
            var outputByOriginal = new Dictionary<Variable, Formal>();
            foreach (var variable in outputVariables)
            {
                var formal = new Formal(variable.tok,
                    new TypedIdent(variable.TypedIdent.tok, "out_" + variable.Name,
                        variable.TypedIdent.Type), false);
                outputs.Add(formal);
                outputByOriginal.Add(variable, formal);
            }
            var helperLocals = new List<Variable>();
            var localByOriginal = new Dictionary<Variable, LocalVariable>();
            foreach (var variable in callerVariables.Where(variable => footprint.Contains(variable) &&
                         !outputByOriginal.ContainsKey(variable) &&
                         (targets.Contains(variable) || !inputByOriginal.ContainsKey(variable))))
            {
                var local = new LocalVariable(variable.tok,
                    new TypedIdent(variable.TypedIdent.tok, "$local$" + variable.Name,
                        variable.TypedIdent.Type));
                helperLocals.Add(local);
                localByOriginal.Add(variable, local);
            }
            Formal exitOutput = null;
            if (regions.Any(region => region.Continuations.Count > 1))
            {
                exitOutput = new Formal(Token.NoToken,
                    new TypedIdent(Token.NoToken, "$exit", Microsoft.Boogie.Type.Int), false);
                outputs.Add(exitOutput);
            }

            var substitutionMap = new Dictionary<Variable, Expr>();
            foreach (var variable in callerVariables.Where(footprint.Contains))
            {
                if (outputByOriginal.TryGetValue(variable, out var output))
                    substitutionMap[variable] = new IdentifierExpr(Token.NoToken, output);
                else if (localByOriginal.TryGetValue(variable, out var local))
                    substitutionMap[variable] = new IdentifierExpr(Token.NoToken, local);
                else if (inputByOriginal.TryGetValue(variable, out var input))
                    substitutionMap[variable] = new IdentifierExpr(Token.NoToken, input);
            }
            var substitution = Substituter.SubstitutionFromDictionary(substitutionMap);
            var helperBlocks = new List<Block>();
            var entryTargets = new List<Block>();
            var returnBlock = exitOutput == null
                ? new Block(Token.NoToken, "$outline_return", new List<Cmd>(), new ReturnCmd(Token.NoToken))
                : null;

            for (var index = 0; index < regions.Count; index++)
            {
                var region = regions[index];
                var blockMap = new Dictionary<Block, Block>();
                var exits = new Dictionary<Block, Block>();
                for (var exitIndex = 0; exitIndex < region.Continuations.Count; exitIndex++)
                {
                    if (exitOutput == null)
                    {
                        exits[region.Continuations[exitIndex]] = returnBlock;
                    }
                    else
                    {
                        var assignExit = new AssignCmd(Token.NoToken,
                            new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken,
                                new IdentifierExpr(Token.NoToken, exitOutput)) },
                            new List<Expr> { Expr.Literal(exitIndex) });
                        var exitBlock = new Block(Token.NoToken,
                            "$arm" + index + "$exit" + exitIndex,
                            new List<Cmd> { assignExit }, new ReturnCmd(Token.NoToken));
                        exits[region.Continuations[exitIndex]] = exitBlock;
                        helperBlocks.Add(exitBlock);
                    }
                }
                foreach (var oldBlock in region.Blocks)
                {
                    blockMap[oldBlock] = new Block(oldBlock.tok,
                        "$arm" + index + "$" + oldBlock.Label,
                        Substituter.Apply(substitution, oldBlock.Cmds), null);
                    traceMapping.BlockLabels.Add(blockMap[oldBlock].Label, oldBlock.Label);
                }
                foreach (var oldBlock in region.Blocks)
                {
                    var oldGoto = (GotoCmd)oldBlock.TransferCmd;
                    var targetsForGoto = oldGoto.LabelTargets.Select(target =>
                        blockMap.TryGetValue(target, out var mapped) ? mapped : exits[target]).Distinct().ToList();
                    blockMap[oldBlock].TransferCmd = new GotoCmd(oldGoto.tok,
                        targetsForGoto.Select(target => target.Label).ToList(), targetsForGoto);
                }
                Block armEntry = blockMap[region.Root];
                if (selector != null)
                {
                    var guard = new Block(Token.NoToken, "$arm" + index + "$guard",
                        new List<Cmd> { new AssumeCmd(Token.NoToken,
                            Expr.Eq(new IdentifierExpr(Token.NoToken, selector), Expr.Literal(index))) },
                        new GotoCmd(Token.NoToken, new List<string> { armEntry.Label },
                            new List<Block> { armEntry }));
                    helperBlocks.Add(guard);
                    entryTargets.Add(guard);
                }
                else
                {
                    entryTargets.Add(armEntry);
                }
                helperBlocks.AddRange(blockMap.Values);
            }

            var initialization = new List<Cmd>();
            var initializedTargets = outputVariables.Where(inputByOriginal.ContainsKey)
                .Concat(localByOriginal.Keys.Where(inputByOriginal.ContainsKey)).ToList();
            if (initializedTargets.Count > 0)
            {
                initialization.Add(new AssignCmd(Token.NoToken,
                    initializedTargets.Select(variable => (AssignLhs)new SimpleAssignLhs(Token.NoToken,
                        substitutionMap[variable] as IdentifierExpr)).ToList(),
                    initializedTargets.Select(variable => (Expr)new IdentifierExpr(Token.NoToken,
                        inputByOriginal[variable])).ToList()));
            }
            var entry = new Block(Token.NoToken, "$outline_entry", initialization,
                new GotoCmd(Token.NoToken, entryTargets.Select(target => target.Label).ToList(), entryTargets));
            helperBlocks.Insert(0, entry);
            if (returnBlock != null)
                helperBlocks.Add(returnBlock);

            var globalMods = new HashSet<Variable>(targets.Where(variable => variable is GlobalVariable));
            foreach (var call in allBlocks.SelectMany(block => block.Cmds).OfType<CallCmd>())
            {
                if (call.Proc != null)
                    globalMods.UnionWith(call.Proc.Modifies.Select(mod => mod.Decl));
            }
            var modifies = globalMods.OfType<GlobalVariable>()
                .Select(variable => new IdentifierExpr(Token.NoToken, variable)).ToList();
            var attributes = new QKeyValue(Token.NoToken, "corral_outlined", new List<object>(), null);
            var procedure = new Procedure(Token.NoToken, name, new List<TypeVariable>(), inputs, outputs,
                false, new List<Requires>(), new List<Requires>(), new List<Ensures>(),
                new List<MeasureCmd>(), modifies, attributes);
            var implementation = new Implementation(Token.NoToken, name, new List<TypeVariable>(),
                inputs, outputs, helperLocals, helperBlocks, attributes);
            implementation.Proc = procedure;

            SiProfile.Write("OUTLINE_HELPER",
                ("implementation", caller.Name),
                ("callee", name),
                ("outline_mode", ModeName(ConfiguredMode)),
                ("count", SiProfile.Number(regions.Count)),
                ("live_ins", SiProfile.Number(stateVariables.Count)),
                ("live_outs", SiProfile.Number(outputVariables.Count)),
                ("internal_locals", SiProfile.Number(helperLocals.Count)),
                ("details", "blocks=" + helperBlocks.Count));

            for (var index = 0; index < regions.Count; index++)
            {
                var callInputs = new List<Expr>();
                if (selector != null)
                    callInputs.Add(Expr.Literal(index));
                callInputs.AddRange(stateVariables.Select(variable =>
                    (Expr)new IdentifierExpr(Token.NoToken, variable)));
                var callOutputs = outputVariables.Select(variable =>
                    new IdentifierExpr(Token.NoToken, variable)).ToList();
                LocalVariable callerExit = null;
                if (exitOutput != null)
                {
                    callerExit = new LocalVariable(Token.NoToken,
                        new TypedIdent(Token.NoToken, "$outline_exit$" + nextCallId,
                            Microsoft.Boogie.Type.Int));
                    caller.LocVars.Add(callerExit);
                    callOutputs.Add(new IdentifierExpr(Token.NoToken, callerExit));
                }
                var call = new CallCmd(regions[index].Root.tok, name, callInputs, callOutputs,
                    new QKeyValue(Token.NoToken, "si_unique_call",
                        new List<object> { Expr.Literal(nextCallId++) }, null));
                call.Proc = procedure;
                regions[index].Root.Cmds = new List<Cmd> { call };
                if (regions[index].Continuations.Count == 1)
                {
                    regions[index].Root.TransferCmd = new GotoCmd(Token.NoToken,
                        new List<string> { regions[index].Continuations[0].Label },
                        new List<Block> { regions[index].Continuations[0] });
                }
                else
                {
                    var dispatchBlocks = new List<Block>();
                    for (var exitIndex = 0; exitIndex < regions[index].Continuations.Count; exitIndex++)
                    {
                        var target = regions[index].Continuations[exitIndex];
                        var guard = new Block(Token.NoToken,
                            "$outline_exit_dispatch$" + nextCallId + "$" + exitIndex,
                            new List<Cmd> { new AssumeCmd(Token.NoToken,
                                Expr.Eq(new IdentifierExpr(Token.NoToken, callerExit), Expr.Literal(exitIndex))) },
                            new GotoCmd(Token.NoToken, new List<string> { target.Label },
                                new List<Block> { target }));
                        dispatchBlocks.Add(guard);
                    }
                    caller.Blocks.AddRange(dispatchBlocks);
                    regions[index].Root.TransferCmd = new GotoCmd(Token.NoToken,
                        dispatchBlocks.Select(block => block.Label).ToList(), dispatchBlocks);
                }
            }
            return Tuple.Create(procedure, implementation);
        }

        private static int NextCallId(Program program)
        {
            var maximum = program.Implementations.SelectMany(implementation => implementation.Blocks)
                .SelectMany(block => block.Cmds).OfType<CallCmd>()
                .Select(call => QKeyValue.FindIntAttribute(call.Attributes, "si_unique_call", 0))
                .DefaultIfEmpty(0).Max();
            return maximum + 1;
        }

        private static string FreshName(HashSet<string> existingNames, string implementation)
        {
            while (true)
            {
                var name = "$corral_outline$" + implementation + "$" + syntheticCounter++;
                if (existingNames.Add(name))
                    return name;
            }
        }

        private static int ReadInt(string name, int fallback, int minimum)
        {
            var text = Environment.GetEnvironmentVariable(name);
            if (!int.TryParse(text, NumberStyles.Integer, CultureInfo.InvariantCulture, out var value))
                return fallback;
            return Math.Max(minimum, value);
        }

        private static string ModeName(Mode mode)
        {
            return mode == Mode.DispatcherArms ? "dispatcher-arms" :
                mode == Mode.WeightedGroups ? "weighted-groups" : "disabled";
        }
    }

    public sealed class DispatcherOutliningPass : cba.CompilerPass
    {
        private DispatcherOutlining.Result result;

        public DispatcherOutliningPass()
        {
            passName = "Dispatcher arm outlining";
        }

        public override CBAProgram runCBAPass(CBAProgram program)
        {
            result = DispatcherOutlining.Apply(program);
            if (result.Changed)
            {
                BoogieUtil.ResolveProgram(program);
                BoogieUtil.TypecheckProgram(program);
            }
            return program;
        }

        public override ErrorTrace mapBackTrace(ErrorTrace trace)
        {
            return result == null ? trace : result.MapBackTrace(trace);
        }
    }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;
using cba;
using System.IO;

namespace cba
{
    public class Driver
    {

        static int Main(string[] args)
        {
            try
            {
                return run(args);
            } 
            catch (InvalidInput e)
            {
                Console.WriteLine();
                Console.WriteLine("Error, Invalid input: {0}", e.Message);
                return 1;
            }
            catch (InternalError e)
            {
                Console.WriteLine();
                Console.WriteLine("Error, internal bug: {0}", e.Message);
                return 1;
            }
            catch (UsageError e)
            {
                Console.WriteLine();
                Console.WriteLine("Usage error: {0}", e.Message);
                Configs.usage();
                return 1;
            }
            catch (NormalExit e)
            {
                Console.WriteLine();
                Console.WriteLine("Stopping: {0}", e.Message);
                return 1;
            } 
            catch (OutOfMemoryException e)
            {
                Console.WriteLine();
                Console.WriteLine("Stopping: {0}", e.Message);
                return 1;
            } 
        }

        public static string VersionInfo()
        {
            var fileName = System.Reflection.Assembly.GetExecutingAssembly().Location;
            var version = System.Diagnostics.FileVersionInfo.GetVersionInfo(fileName).FileVersion;
            return version;
        }

        public static void Initialize(Configs config)
        {
            // Batch-mode GC is best for performance
            System.Runtime.GCSettings.LatencyMode = System.Runtime.GCLatencyMode.Batch;

            #region Set global flags
            GlobalConfig.genCTrace = config.genCTrace;
            GlobalConfig.useArrayTheory = config.arrayTheory;
            GlobalConfig.addRaiseException = true;
            GlobalConfig.recursionBound = config.recursionBound;
            GlobalConfig.timeOut = config.timeout;
            GlobalConfig.catchAllExceptions = false;
            GlobalConfig.addInvariants = 2;

            CoreLib.StratifiedInlining.StratifiedInliningVerbose = config.verboseMode;

            ProgTransformation.TransformationPass.writeAllFiles = false;
            Log.noDebuggingOutput = true;
            Log.verbose_level = config.verboseMode;
            #endregion

            ConfigManager.Initialize(config);

            string boogieOptions = "";
            boogieOptions += config.boogieOpts;

            boogieOptions += "/extractLoops /errorLimit:1 ";

            boogieOptions += string.Format("/recursionBound:{0} ", config.recursionBound);

            // Initialize Boogie
            CommandLineOptions.Clo.PrintInstrumented = true;
            CommandLineOptions.Clo.ProcedureInlining = CommandLineOptions.Inlining.Assume;
            CommandLineOptions.Clo.TypeEncodingMethod = CommandLineOptions.TypeEncoding.Monomorphic;

            // /noRemoveEmptyBlocks is needed for field refinement. It ensures that
            // we get an actual path in the program (so that we can concretize it)
            boogieOptions +=
                "/removeEmptyBlocks:0 /coalesceBlocks:0 " +
                "/subsumption:0 ";

            InstrumentationConfig.UseOldInstrumentation = false;
            VariableSlicing.UseSimpleSlicing = false;
            InstrumentationConfig.raiseExceptionBeforeAllProcedures = false;

            if (GlobalConfig.useArrayTheory == ArrayTheoryOptions.STRONG)
                boogieOptions += " /useArrayTheory";
            else if (GlobalConfig.useArrayTheory == ArrayTheoryOptions.WEAK)
            {
                boogieOptions += " /useArrayTheory";
                boogieOptions += " /proverOpt:O:smt.array.extensional=false";
            }

            if (BoogieUtil.InitializeBoogie(boogieOptions))
                throw new InternalError("Cannot initialize Boogie");

            if (CommandLineOptions.Clo.UseProverEvaluate)
                CommandLineOptions.Clo.StratifiedInliningWithoutModels = true;

            GlobalConfig.corralStartTime = DateTime.Now;
        }

        public static int run(string[] args) 
        {
            ////////////////////////////////////
            // Input and initialization phase
            ////////////////////////////////////

            Console.WriteLine("Corral program verifier version {0}", VersionInfo());

            Configs config = Configs.parseCommandLine(args);
            CommandLineOptions.Install(new CommandLineOptions());

            if (!System.IO.File.Exists(config.inputFile))
            {
                throw new UsageError(string.Format("Input file {0} does not exist", config.inputFile));
            }

            Initialize(config);

            var startTime = DateTime.Now;

            ////////////////////////////////////
            // Initial program rewriting
            ////////////////////////////////////

            #region initial program rewriting

            var inputProg = GetInputProgram(config);
            if (inputProg == null) return 0;

            // infer loop bound 
            if (config.maxStaticLoopBound > 0)
            {
                // abstract away globals (except for thread_locals)
                var thread_locals = new HashSet<string>(inputProg.getProgram()
                    .TopLevelDeclarations.OfType<GlobalVariable>()
                    .Where(gv => QKeyValue.FindBoolAttribute(gv.Attributes, LanguageSemantics.ThreadLocalAttr))
                    .Select(gv => gv.Name));
                var abs = new VariableSlicePass(VarSet.ToVarSet(thread_locals, inputProg.getProgram()));

                var lprog = abs.run(inputProg);

                // extract loops
                var el = new ExtractLoopsPass(true);
                lprog = el.run(lprog);

                var LBoptions = ConfigManager.progVerifyOptions.Copy();
                LBoptions.useDI = false;
                LBoptions.useFwdBck = false;
                LBoptions.NonUniformUnfolding = false;
                LBoptions.extraFlags = new HashSet<string>();
                LBoptions.newStratifiedInliningAlgo = "";
                ConfigManager.progVerifyOptions.extraRecBound = new Dictionary<string, int>();

                try
                {
                    var bounds = LoopBound.Compute(lprog.getCBAProgram(), config.maxStaticLoopBound, GlobalConfig.annotations, LBoptions);
                    bounds.Iter(kvp => ConfigManager.progVerifyOptions.extraRecBound.Add(kvp.Key, kvp.Value));
                }
                catch (CoreLib.InsufficientDetailsToConstructCexPath e)
                {
                    Console.WriteLine("Exception: {0}", e.Message);
                    Console.WriteLine("Skipping LB inferrence");
                }

                Console.WriteLine("LB: Took {0} s", LoopBound.timeTaken.TotalSeconds.ToString("F2"));
            }

            //////
            // Other transformations
            //////

            // Rewrite assert commands
            RewriteAssertsPass apass = new RewriteAssertsPass();
            var curr = apass.run(inputProg);

            // Rewrite call commands 
            RewriteCallCmdsPass rcalls = new RewriteCallCmdsPass(true);
            curr = rcalls.run(curr);

            // Prune
            PruneProgramPass.RemoveUnreachable = true;
            var prune = new PruneProgramPass(false);
            curr = prune.run(curr);
            PruneProgramPass.RemoveUnreachable = false;

            // Sequential instrumentation
            ExtractLoopsPass elPass = null;
            var seqInstr = new SequentialInstrumentation();
            if (GlobalConfig.isSingleThreaded)
            {
                curr = seqInstr.run(curr);

                // Flag settings for sequential programs
                VerificationPass.usePruning = false;

                if (!config.useProverEvaluate)
                {
                    ConfigManager.progVerifyOptions.StratifiedInliningWithoutModels = true;
                    if (config.printData == 0)
                        ConfigManager.pathVerifyOptions.StratifiedInliningWithoutModels = true;
                }

                // extract loops
                if (GlobalConfig.InferPass != null)
                {
                    elPass = new ExtractLoopsPass(true);
                    curr = elPass.run(curr);
                    CommandLineOptions.Clo.ExtractLoops = false;
                }
            }
            else
            {
                seqInstr = null;
                if (GlobalConfig.InferPass != null)
                {
                    throw new InvalidInput("We currently don't support summaries for concurrent programs");
                }
                if (config.NumCex > 1)
                {
                    throw new InvalidInput("Multiple counterexamples not yet supported for concurrent programs");
                }

                GlobalConfig.InferPass = null;
            }

            ProgTransformation.PersistentProgram.FreeParserMemory();
            #endregion

            // For debugging, create an Action for printing a trace at the source level
            var passes = new List<CompilerPass>(new CompilerPass[] { elPass, seqInstr, prune, rcalls, apass });
            var printTrace = new Action<ErrorTrace, string>((trace, fileName) =>
                {
                    if (GlobalConfig.genCTrace == null)
                        return;
                    passes.Where(p => p != null)
                        .Iter(p => trace = p.mapBackTrace(trace));
                    PrintConcurrentProgramPath.printCTrace(inputProg, trace, fileName);
                    apass.reset();
                });

            var cex = config.NumCex;

            do
            {
                ////////////////////////////////////
                // Verification phase
                ////////////////////////////////////

                Log.WriteMemUsage();

                var refinementState = new RefinementState(curr, new HashSet<string>(), false);

                ErrorTrace cexTrace = null;
                checkAndRefine(curr, refinementState, printTrace, out cexTrace);

                ////////////////////////////////////
                // Output Phase
                ////////////////////////////////////

                var currTrace = cexTrace == null ? null : cexTrace.Copy();

                if (cexTrace != null)
                {
                    if (elPass != null) cexTrace = elPass.mapBackTrace(cexTrace);
                    if (seqInstr != null) cexTrace = seqInstr.mapBackTrace(cexTrace);
                    cexTrace = prune.mapBackTrace(cexTrace);
                    cexTrace = rcalls.mapBackTrace(cexTrace);

                    cexTrace = apass.mapBackTrace(cexTrace);

                    var traceName = "corral_out";
                    if (config.NumCex > 1)
                        traceName += (config.NumCex - cex);

                    if (!config.noTraceOnDisk)
                    {
                        Console.WriteLine("Dumping trace as file {0}", traceName);
                    }

                    if (GlobalConfig.genCTrace != null)
                    {
                        PrintConcurrentProgramPath.traceFormat = GlobalConfig.genCTrace.Value;
                        PrintConcurrentProgramPath.printCTrace(inputProg, cexTrace, config.noTraceOnDisk ? null : traceName);
                    }
                    else
                    {
                        if(!config.noTraceOnDisk)
                            PrintConcurrentProgramPath.print(inputProg, cexTrace, traceName);

                        var init = BoogieUtil.ReadAndOnlyResolve(config.inputFile);
                        PrintConcurrentProgramPath.print(init, cexTrace, config.inputFile);
                    }

                    apass.reset();
                }

                cex--;
                if (cexTrace == null) cex = 0;

                // Disable the failing assertion in the program
                if (cex > 0 && seqInstr != null)
                    curr = DisableAssert(curr, currTrace, seqInstr.assertsPassedName);

                // Reset corral state
                ConfigManager.progVerifyOptions.CallTree = new HashSet<string>();

                // print timing information
                Stats.printStats();
                Log.WriteLine(string.Format("Number of procedures inlined: {0}", Stats.ProgCallTreeSize));
                Log.WriteLine(string.Format("Number of variables tracked: {0}", refinementState.getVars().Variables.Count));
                Stats.ProgCallTreeSize = 0;

            } while (cex > 0);

            var endTime = DateTime.Now;

            Log.WriteLine(string.Format("Total Time: {0} s", (endTime - startTime).TotalSeconds));

            // Add our CPU time to Z3's CPU time reported by SMTLibProcess and print it
            System.TimeSpan TotalUserTime = System.Diagnostics.Process.GetCurrentProcess().UserProcessorTime;
            TotalUserTime += Microsoft.Boogie.SMTLib.SMTLibProcess.TotalUserTime;
            Log.WriteLine(string.Format("Total User CPU time: {0} s", TotalUserTime.TotalSeconds));


            Log.Close();

            return 0;
        }

        private static PersistentCBAProgram DisableAssert(PersistentCBAProgram program, ErrorTrace trace, string assertsPassed)
        {
            var prog = program.getCBAProgram();

            // walk the trace and program in lock step -- find the failing assertion
            var location = ErrorTrace.FindCmd(prog, trace, c => (c is AssumeCmd) && QKeyValue.FindBoolAttribute((c as AssumeCmd).Attributes, RewriteAsserts.AssertIdentificationAttribute));
            Debug.Assert(location != null);

            // Disable assert
            var acmd = location.Item2.Cmds[location.Item3] as AssumeCmd;
            Debug.Assert(acmd != null);
            acmd.Expr = Expr.False;

            // Disable assignment to assertsPassed (for better mod-set invariants)
            for(int i = 0; i < location.Item2.Cmds.Count; i++) 
            {
                var cmd = location.Item2.Cmds[i] as AssignCmd;
                if (cmd == null) continue;
                if (cmd.Lhss.Any(lhs => lhs.DeepAssignedVariable.Name == assertsPassed))
                {
                    location.Item2.Cmds[i] = BoogieAstFactory.MkAssume(Expr.True);
                }
            }

            BoogieUtil.PrintProgram(prog, "next.bpl");

            return new PersistentCBAProgram(prog, prog.mainProcName, prog.contextBound, program.mode);
        }

        public static PersistentCBAProgram GetInputProgram(Configs config)
        {
            // This is to check the input program for parsing and resolution
            // errors. We check for type errors later
            Program init = BoogieUtil.ReadAndOnlyResolve(config.inputFile);

            // Gather templates for Houdini
            var extraVars = findTemplates(init, config);

            #region Check that the input is well-formed

            //////////////////////////////////////////
            // Make sure that the input is well-formed
            if (config.mainProcName == null)
            {
                List<string> entrypoints = EntrypointScanner.FindEntrypoint(init);
                if (entrypoints.Count == 0)
                    throw new InvalidInput("Main procedure not specified");
                config.mainProcName = entrypoints[0];
            }

            if (BoogieUtil.findProcedureImpl(init.TopLevelDeclarations, config.mainProcName) == null)
            {
                throw new InvalidInput("Implementation of main procedure not found");
            }
            
            if (SequentialInstrumentation.isSingleThreadProgram(init, config.mainProcName))
            {
                GlobalConfig.isSingleThreaded = true;
                Console.WriteLine("Single threaded program detected");
            }

            if (!GlobalConfig.isSingleThreaded)
            {
                try
                {
                    WellFormedProg.check(init);
                }
                catch (InvalidInput e)
                {
                    throw new InvalidInput("Input Program not well-formed.\n" + e.Message);
                }
            }

            #endregion

            // force inline
            foreach (var impl in init.TopLevelDeclarations.OfType<Implementation>())
            {
                if (BoogieUtil.checkAttrExists("inline", impl.Attributes) || BoogieUtil.checkAttrExists("inline", impl.Proc.Attributes))
                    impl.AddAttribute(CoreLib.StratifiedInlining.ForceInlineAttr);
            }

            // CodeExpr support
            PreProcessCodeExpr(init);

            foreach(var decl in init.TopLevelDeclarations)
                    decl.Attributes = BoogieUtil.removeAttr("inline", decl.Attributes);

            // Add unique ids on calls
            var addIds = new AddUniqueCallIds();
            addIds.VisitProgram(init);

            // Update mod sets
            BoogieUtil.DoModSetAnalysis(init);

            // Now we can typecheck
            CommandLineOptions.Clo.DoModSetAnalysis = true;
            if (BoogieUtil.TypecheckProgram(init, config.inputFile))
            {
                BoogieUtil.PrintProgram(init, "error.bpl");
                throw new InvalidProg("Cannot typecheck " + config.inputFile);
            }
            CommandLineOptions.Clo.DoModSetAnalysis = false;

            // thread-local variables are always tracked
            var globals = BoogieUtil.GetGlobalVariables(init);

            // Gather the set of initially tracked variables
            var initialTrackedVars = getTrackedVars(init, config);

            // Gather source info
            if (GlobalConfig.genCTrace != null)
            {
                PrintConcurrentProgramPath.traceFormat = GlobalConfig.genCTrace.Value;
                PrintConcurrentProgramPath.printData = config.printData;
                PrintConcurrentProgramPath.gatherCSourceLineInfo(init);
            }

            var inputProg = new PersistentCBAProgram(init, config.mainProcName, GlobalConfig.isSingleThreaded ? 1 : config.contextBound);
            ProgTransformation.PersistentProgram.FreeParserMemory();
            
            return inputProg;
        }

        // Inline procedures called from inside a CodeExpr
        public static void PreProcessCodeExpr(Program program)
        {
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                impl.OriginalBlocks = impl.Blocks;
                impl.OriginalLocVars = impl.LocVars;
            }
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                if (CommandLineOptions.Clo.UserWantsToCheckRoutine(impl.Name) && !impl.SkipVerification)
                {
                    CodeExprInliner.ProcessImplementation(program, impl);
                }
            }
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                impl.OriginalBlocks = null;
                impl.OriginalLocVars = null;
            }
        }

        // Inline procedures call from inside a CodeExpr
        class CodeExprInliner : Inliner
        {
            Dictionary<Declaration, QKeyValue> declToAnnotations;

            public CodeExprInliner(Program program)
                : base(program, null, -1)
            {
                this.declToAnnotations = new Dictionary<Declaration, QKeyValue>();
                // save annotation
                foreach (var decl in program.TopLevelDeclarations)
                {
                    declToAnnotations.Add(decl, decl.Attributes);
                    decl.Attributes = null;
                }
            }

            new public static void ProcessImplementation(Program program, Implementation impl)
            {
                var ce = new CodeExprInliner(program);
                ProcessImplementation(program, impl, ce);
                ce.RestoreAnnotations();
            }

            public override Expr VisitCodeExpr(CodeExpr node)
            {
                // Install {:inline} annotations
                RestoreAnnotations();

                var ret = base.VisitCodeExpr(node);

                // remove {:inline} annotation
                RemoveAnnotations();

                return ret;
            }

            void RestoreAnnotations()
            {
                foreach (var decl in program.TopLevelDeclarations)
                {
                    if (!declToAnnotations.ContainsKey(decl)) continue;
                    decl.Attributes = declToAnnotations[decl];
                }
            }

            void RemoveAnnotations()
            {
                foreach (var decl in program.TopLevelDeclarations)
                {
                    decl.Attributes = null;
                }
            }

        }

        public static void InlineProcedures(Program program)
        {
            var si = CommandLineOptions.Clo.StratifiedInlining;
            CommandLineOptions.Clo.StratifiedInlining = 0;
            ExecutionEngine.EliminateDeadVariables(program);
            ExecutionEngine.Inline(program);
            CommandLineOptions.Clo.StratifiedInlining = si;
        }

        // Stats: LOC on trace and number of branches
        public static void TraceStats(ErrorTrace trace, Dictionary<string, Implementation> nameImplMap, ref int loc, ref HashSet<int> branches)
        {
            if (trace == null || !nameImplMap.ContainsKey(trace.procName))
                return;

            var impl = nameImplMap[trace.procName];
            var nb = new HashSet<int>();
            var blockMap = BoogieUtil.labelBlockMapping(impl);
            var first = true;

            foreach (var blk in trace.Blocks)
            {
                if (first)
                {
                    first = false;
                    continue;
                }

                if (blockMap.ContainsKey(blk.blockName))
                {
                    var ablk = blockMap[blk.blockName];
                    foreach (var acmd in ablk.Cmds.OfType<PredicateCmd>())
                    {
                        if (QKeyValue.FindStringAttribute(acmd.Attributes, "sourceFile") != null) loc++;
                        if (QKeyValue.FindIntAttribute(acmd.Attributes, "breadcrumb", -1) != -1)
                            nb.Add(QKeyValue.FindIntAttribute(acmd.Attributes, "breadcrumb", -1));
                    }
                }

                foreach (var ccmd in blk.Cmds.OfType<CallInstr>())
                {
                    TraceStats(ccmd.calleeTrace, nameImplMap, ref loc, ref branches);
                }
            }

            branches.UnionWith(nb);
        }

        public static HashSet<string> findTemplates(Program program, Configs config)
        {
            var templateVarNames = new HashSet<Variable>();
            List<Ensures> ens = new List<Ensures>();
            List<Requires> req = new List<Requires>();
            var extra = new HashSet<string>();

            var newDecls = new List<Declaration>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, "template"))
                {
                    newDecls.Add(decl);
                    continue;
                }
                if (decl is GlobalVariable)
                {
                    templateVarNames.Add((decl as Variable));
                }
                else if (decl is Procedure)
                {
                    var proc = decl as Procedure;

                    proc.Ensures.OfType<Ensures>().Where(e =>
                        (!BoogieUtil.checkAttrExists("abshoudini", e.Attributes)))
                        .Iter(e => ens.Add(e));

                    proc.Requires.OfType<Requires>().Where(r =>
                        (!BoogieUtil.checkAttrExists("abshoudini", r.Attributes)))
                        .Iter(r => req.Add(r));
                }

            }
            foreach (Ensures en in ens)
            {
                var gu = new GlobalVarsUsed();
                gu.VisitEnsures(en);
                extra.UnionWith(gu.globalsUsed);
            }
            foreach (Requires re in req)
            {
                var gu = new GlobalVarsUsed();
                gu.VisitRequires(re);
                extra.UnionWith(gu.globalsUsed);
            }
            foreach (var t in templateVarNames)
            {
                extra.Remove(t.Name);
            }

            program.TopLevelDeclarations = newDecls;
            GlobalConfig.InferPass = new ContractInfer(templateVarNames, req, ens, -1, -1);
            return extra;
        }

        // For debugging (printing abstract traces)
        static int traceCounterDbg = 0;

        // Check program "inputProg" using variable abstraction
        public static bool checkAndRefine(PersistentCBAProgram prog, RefinementState refinementState, Action<ErrorTrace, string> printTrace, out ErrorTrace cexTrace)
        {
            cexTrace = null;
            var outcomeSuccess = true;
            var finerCheck = false;
            var lightweight = false;
            var optRefinementLoop = true;

            #region flag setting
            if (GlobalConfig.refinementAlgo[3] == 'f')
                finerCheck = false;
            else 
                finerCheck = GlobalConfig.isSingleThreaded ? false : true;

            if (GlobalConfig.refinementAlgo[2] == 'f')
                lightweight = false;
            else
                lightweight = true;

            if (GlobalConfig.refinementAlgo[1] == 'f')
                GeneralRefinementScheme.useHierarchicalSearch = false;
            else
                GeneralRefinementScheme.useHierarchicalSearch = true;

            if (GlobalConfig.refinementAlgo[0] == 'f')
                optRefinementLoop = false;
            else
                optRefinementLoop = true;
            #endregion

            // This loop exits only under two conditions: 
            //     - The abstracted program had no errors
            //     - The concretized counterexample has an error

            refinementState.Push();

            while (true)
            {
                refinementState.Push();
                PersistentCBAProgram counterexample = null;

                if (GlobalConfig.timeOutReached())
                    throw new InternalError("Timeout reached!");

                ProgTransformation.PersistentProgramIO.CheckMemoryPressure();

                if (!GlobalConfig.useLocalVariableAbstraction)
                    Log.WriteLine("Verifying program while tracking: {0}", refinementState.getVars().Variables.Print());
                else
                    Log.WriteLine("Verifying program while tracking: {0}", refinementState.getVars().ToString());

                // This records the transformation made when "curr" is
                // transformed to "counterexample"
                InsertionTrans tinfo = null;

                bool success =
                    CBADriver.checkProgram(ref prog, refinementState.getVars(), true, out counterexample, out tinfo, out cexTrace);

                if (success) {
                    Log.WriteLine("Program has no bugs");
                    if (CBADriver.reachedBound)
                    {
                        Log.WriteLine("Reached recursion bound of " + GlobalConfig.recursionBound.ToString());
                    }
                    outcomeSuccess = true;
                    break;
                }

                Log.Write("Program has a potential bug: ");

                if (!lightweight) counterexample.mode = ConcurrencyMode.AnyInterleaving;

                refinementState.Add(new TraceMapping(tinfo));

                // Check if true bug. Otherwise, gather variables to track                
                if (optRefinementLoop)
                    success = checkAndRefinePathFewPasses(counterexample, refinementState, out cexTrace);
                else
                    success = checkAndRefinePath(counterexample, refinementState, out cexTrace);

                if (!success)
                {
                    // Generate cex in the original program
                    cexTrace = tinfo.mapBackTrace(cexTrace);
                    outcomeSuccess = false;
                    break;
                }

                while (finerCheck)
                {
                    // Expand the check to all possible interleavings contained in counterexample
                    counterexample.mode = ConcurrencyMode.AnyInterleaving;

                    PersistentCBAProgram counterexample2 = null;
                    InsertionTrans tinfo2 = null;
                    ErrorTrace cexTrace2 = null;
                    
                    success =
                        CBADriver.checkPath(counterexample, refinementState.getVars(), true, out counterexample2, out tinfo2, out cexTrace2);

                    // We have enough tracked vars
                    if (success) break;
                    Debug.Assert(counterexample2.mode == ConcurrencyMode.FixedContext);

                    // We don't have enough tracked vars -- track more
                    Log.Write("Program has a potential bug: ");

                    refinementState.Push();
                    refinementState.Add(new TraceMapping(tinfo2));
                    success = checkAndRefinePathFewPasses(counterexample2, refinementState, out cexTrace2);
                    refinementState.Pop();

                    if (!success)
                    {
                        // Generate cex in the original program
                        cexTrace2 = tinfo2.mapBackTrace(cexTrace2);
                        cexTrace = tinfo.mapBackTrace(cexTrace2);
                        outcomeSuccess = false;
                        break;
                    }
                }
                
                refinementState.Pop();

                // We've found a bug
                if (!outcomeSuccess) break;
            }
            
            refinementState.Pop();

            return outcomeSuccess;
        }

        // Does field refinement. It optimizes the flow of CompilerPasses, factoring out the
        // common ones outside the refinement loop
        private static bool checkAndRefinePathFewPasses(PersistentCBAProgram counterexample,
            RefinementState refinementState, out ErrorTrace cexTrace)
        {
            BoogieVerify.setTimeOut(GlobalConfig.getTimeLeft());
            
            // Check if counterexample is valid
            var success = CBADriver.checkPath(counterexample, counterexample.allVars, out cexTrace);

            if (!success)
            {
                Log.WriteLine("True bug");
                return false;
            }
            else
            {
                Log.WriteLine("False bug");
            }

            cexTrace = null;

            StormInstrumentationPass cp1 = null;

            if (!GlobalConfig.isSingleThreaded)
            {
                cp1 = new StormInstrumentationPass();
            }

            var prog = counterexample;
            if (cp1 != null) prog = cp1.run(prog);

            refinementState.Push();

            if (cp1 != null) refinementState.Add(new InstrMapping(cp1));

            ConfigManager.beginRefinement();

            // Compute the new set of tracked variables to rule out this counterexample
            var refine = new GeneralRefinementScheme(new SequentialProgVerifier(), true, prog, refinementState);
            refine.doRefinement();
            if (refine.useZ3Search)
            {
                Stats.pathVerificationQueries++;
                Stats.pathVerificationTime += refine.timeTaken;
            }
            ConfigManager.endRefinement();

            refinementState.Pop();

            return true;
        }

        // Does field refinement
        private static bool checkAndRefinePath(PersistentCBAProgram counterexample,
            RefinementState refinementState, out ErrorTrace cexTrace)
        {
            BoogieVerify.setTimeOut(GlobalConfig.getTimeLeft());

            // Check if counterexample is valid
            var success = CBADriver.checkPath(counterexample, counterexample.allVars, out cexTrace);

            if (!success)
            {
                Log.WriteLine("True bug");
                return false;
            }
            else
            {
                Log.WriteLine("False bug");
            }

            cexTrace = null;

            // Compute the new set of tracked variables to rule out this counterexample
            var refine = new GeneralRefinementScheme(new ConcurrentProgVerifier(), counterexample, refinementState);
            refine.doRefinement();

            return true;

        }

        // Returns the set of all global variables in the program, as well as the ones
        // that need to be tracked initially (according to command-line arguments)
        private static HashSet<string> getTrackedVars(Program prog, Configs config)
        {
            var globalVars = BoogieUtil.GetGlobalVariables(prog);
            VarSet allVars = VarSet.GetAllVars(prog);

            if (config.trackAllVars)
            {
                return allVars.Variables;
            }
            else
            {
                HashSet<string> vs = new HashSet<string>();
                foreach (var x in globalVars)
                {
                    var s = x.Name;
                    if (!LanguageSemantics.isShared(s))
                    {
                        vs.Add(s);
                    }
                }
                return vs;
            }
        }
    }
}

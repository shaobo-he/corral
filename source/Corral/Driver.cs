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

        // The prover option that switches Z3's array extensionality off. It is added in
        // Initialize and taken back out in GetInputProgram when the input turns out to need
        // extensionality; keep the two uses of this literal together.
        private const string arrayExtensionalityOff = "O:smt.array.extensional=false";

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
            GlobalConfig.addInvariants = 2;

            CoreLib.StratifiedInlining.StratifiedInliningVerbose = config.verboseMode;
            BoogieVerify.ignoreAssertMethods = new HashSet<string>();

            ProgTransformation.TransformationPass.writeAllFiles = false;
            Log.noDebuggingOutput = true;
            Log.verbose_level = config.verboseMode;
            #endregion

            ConfigManager.Initialize(config);

            string boogieOptions = "";
            boogieOptions += config.boogieOpts;

            boogieOptions += "/errorLimit:1 ";
            BoogieUtil.RecursionBound = config.recursionBound;

            // Initialize Boogie
            BoogieUtil.BoogieOptions.PrintInstrumented = true;
            BoogieUtil.BoogieOptions.ProcedureInlining = CoreOptions.Inlining.Assume;
            BoogieUtil.BoogieOptions.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
            BoogieUtil.BoogieOptions.EnableUnSatCoreExtract = 1;
            BoogieUtil.BoogieOptions.UseProverEvaluate = true;
            BoogieUtil.BoogieOptions.InferModifies = true;

            // /noRemoveEmptyBlocks is needed for field refinement. It ensures that
            // we get an actual path in the program (so that we can concretize it)
            boogieOptions +=
                "/removeEmptyBlocks:0 /coalesceBlocks:0 " +
                "/subsumption:0 ";

            InstrumentationConfig.UseOldInstrumentation = false;
            VariableSlicing.UseSimpleSlicing = false;
            InstrumentationConfig.raiseExceptionBeforeAllProcedures = false;

            if (GlobalConfig.useArrayTheory == ArrayTheoryOptions.WEAK)
            {
                boogieOptions += " /proverOpt:" + arrayExtensionalityOff;
            }

            if (BoogieUtil.InitializeBoogie(boogieOptions))
                throw new InternalError("Cannot initialize Boogie");

            // Libraries requested with /lib: join the ones a pass-through /bopt:lib: put
            // there. BoogieUtil.ReadAndOnlyResolve is what reads this; nothing in corral
            // calls ExecutionEngine, which is Boogie's own (and only) consumer.
            BoogieUtil.BoogieOptions.Libraries.UnionWith(config.libraries);

            if (BoogieUtil.BoogieOptions.UseProverEvaluate)
                BoogieUtil.BoogieOptions.StratifiedInliningWithoutModels = true;

            GlobalConfig.corralStartTime = DateTime.Now;
        }

        public static int run(string[] args)
        {
            ////////////////////////////////////
            // Input and initialization phase
            ////////////////////////////////////

            Console.WriteLine("Corral program verifier version {0}", VersionInfo());

            Configs config = Configs.parseCommandLine(args);
            BoogieUtil.BoogieOptions = new CommandLineOptions(Console.Out, new ConsolePrinter());

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

            var inputProg = GetInputProgram(config, out var initialTrackedVars);
            if (inputProg == null) return 0;

            // infer loop bound 
            if (config.maxStaticLoopBound > 0)
            {
                // abstract away globals (except for thread_locals)
                var thread_locals = new HashSet<string>(inputProg.getProgram()
                    .TopLevelDeclarations.OfType<GlobalVariable>()
                    .Where(gv => QKeyValue.FindAttribute(gv.Attributes, attr => attr.Key == LanguageSemantics.ThreadLocalAttr) != null)
                    .Select(gv => gv.Name));
                var abs = new VariableSlicePass(VarSet.ToVarSet(thread_locals, inputProg.getProgram()));

                var lprog = abs.run(inputProg);

                // extract loops
                var el = new ExtractLoopsPass(true);
                lprog = el.run(lprog);

                var LBoptions = ConfigManager.progVerifyOptions.Copy();
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
            var seqInstr = new SequentialInstrumentation();
            curr = seqInstr.run(curr);
            initialTrackedVars.Add(seqInstr.assertsPassedName);

            // Flag settings for sequential programs
            VerificationPass.usePruning = false;

            if (!config.useProverEvaluate)
            {
                ConfigManager.progVerifyOptions.StratifiedInliningWithoutModels = true;
                if (config.printData == 0)
                    ConfigManager.pathVerifyOptions.StratifiedInliningWithoutModels = true;
            }

            ProgTransformation.PersistentProgram.FreeParserMemory();
            #endregion

            // For debugging, create an Action for printing a trace at the source level
            var passes = new List<CompilerPass>(new CompilerPass[] { seqInstr, prune, rcalls, apass });
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

                var refinementState = new RefinementState(curr, initialTrackedVars, false);

                ErrorTrace cexTrace = null;
                checkAndRefine(curr, refinementState, printTrace, out cexTrace);

                ////////////////////////////////////
                // Output Phase
                ////////////////////////////////////

                var currTrace = cexTrace == null ? null : cexTrace.Copy();

                if (cexTrace != null)
                {
                    cexTrace = seqInstr.mapBackTrace(cexTrace);
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
                        if (!config.noTraceOnDisk)
                            PrintConcurrentProgramPath.print(inputProg, cexTrace, traceName);

                        var init = BoogieUtil.ReadAndOnlyResolve(config.inputFile);
                        try
                        {
                            // Re-prints the same trace against the *source* program. Monomorphization
                            // renames the implementation of a type-parameterized procedure (foo ->
                            // foo_3), so a trace that enters such a body names a procedure that does
                            // not exist in the source program and this print throws. The verdict and
                            // the trace above are already correct; do not abort the process for it.
                            PrintConcurrentProgramPath.print(init, cexTrace, config.inputFile);
                        }
                        catch (KeyNotFoundException)
                        {
                            Console.WriteLine("Warning: cannot map the trace back to {0} (monomorphized procedure on the path)", config.inputFile);
                        }
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
            var location = ErrorTrace.FindCmd(prog, trace, c => (c is AssumeCmd) && QKeyValue.FindAttribute((c as AssumeCmd).Attributes, attr => attr.Key == RewriteAsserts.AssertIdentificationAttribute) != null);
            Debug.Assert(location != null);

            // Disable assert
            var acmd = location.Item2.Cmds[location.Item3] as AssumeCmd;
            Debug.Assert(acmd != null);
            acmd.Expr = Expr.False;

            // Disable assignment to assertsPassed (for better mod-set invariants)
            for (int i = 0; i < location.Item2.Cmds.Count; i++)
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

        public static PersistentCBAProgram GetInputProgram(Configs config, out HashSet<string> initialTrackedVars)
        {
            // This is to check the input program for parsing and resolution
            // errors. We check for type errors later
            Program init = BoogieUtil.ReadAndOnlyResolve(config.inputFile);



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

            #endregion

            // force inline
            foreach (var impl in init.TopLevelDeclarations.OfType<Implementation>())
            {
                if (BoogieUtil.checkAttrExists("inline", impl.Attributes) || BoogieUtil.checkAttrExists("inline", impl.Proc.Attributes))
                    impl.AddAttribute(CoreLib.StratifiedInlining.ForceInlineAttr);
            }

            // CodeExpr support
            PreProcessCodeExpr(init);

            foreach (var decl in init.TopLevelDeclarations)
                decl.Attributes = BoogieUtil.removeAttr("inline", decl.Attributes);

            // Update mod sets
            BoogieUtil.DoModSetAnalysis(init);

            // Now we can typecheck
            if (BoogieUtil.TypecheckProgram(init, config.inputFile))
            {
                BoogieUtil.PrintProgram(init, "error.bpl");
                throw new InvalidProg("Cannot typecheck " + config.inputFile);
            }

            // Some inputs state their facts as whole-map equalities: Boogie's base.bpl is written
            // that way throughout (IsSubset(a, b) is "MapImp(a, b) == MapConst(true)",
            // base.bpl:36-39; Set_IsDisjoint compares two Sets, base.bpl:168-172). Establishing
            // such an equality from pointwise facts needs Z3's array extensionality, which
            // Initialize switched off above, so those inputs got a spurious "True bug". Switch it
            // back on for them. Inputs that never compare two maps -- which is all of SMACK's
            // output -- keep the option and are handed to the prover exactly as before.
            // Has to run after the typecheck above: the detector reads Expr.Type.
            if (GlobalConfig.useArrayTheory == ArrayTheoryOptions.WEAK && UsesMapEquality(init))
            {
                BoogieUtil.BoogieOptions.ProverOptions.RemoveAll(
                    o => o.Replace(" ", "").Equals(arrayExtensionalityOff, StringComparison.OrdinalIgnoreCase));
            }

            // Drop "pure" from any procedure that has a body. A pure procedure is resolved
            // StateLess (Implementation.cs:578), so it may not mention a global at all, and
            // corral's error flag is a global: instrumenting one produces "cannot refer to a
            // global variable in this context: assertsPassed" and the run dies as an internal
            // error. base.bpl has four such procedures (Map_MakeEmpty, Loc_New, Tag_New,
            // Tags_New), so calling any of them was fatal.
            //
            // Skipping instrumentation instead would be wrong: a pure procedure body may
            // contain a real assert, and Boogie does check it (verified against stock Boogie),
            // so leaving it untracked would lose a bug. Purity is a well-formedness property of
            // the input, and the input has just been resolved and typechecked with it enforced;
            // it constrains nothing that corral does downstream, since corral inlines bodies
            // rather than reasoning about Civl movers. Bodiless pure procedures keep the marker
            // -- nothing instruments them, and a non-pure caller may still call them
            // (CallCmd.cs:239 only restricts calls made *from* a pure procedure).
            foreach (var impl in init.TopLevelDeclarations.OfType<Implementation>())
            {
                if (impl.Proc != null)
                    impl.Proc.IsPure = false;
            }

            // Get rid of polymorphism. Boogie's own ExecutionEngine does this right after
            // typechecking; corral never did, so a polymorphic declaration (e.g. any of the
            // datatypes in Boogie's base.bpl) reached the prover, where DeclareType threw
            // ProverException("Polymorphic datatypes are not supported"). That exception was
            // swallowed in BoogieVerify.Verify, which then reported "Program has no bugs".
            if (MonomorphismChecker.IsMonomorphic(init))
            {
                BoogieUtil.BoogieOptions.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
            }
            else if (BoogieUtil.BoogieOptions.TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic)
            {
                // Boogie's monomorphizer instantiates the *body* of a type-parameterized
                // procedure at a call site's actual type arguments only when that procedure's
                // implementation (or its procedure) carries {:inline}:
                // MonomorphizationVisitor.InlineCallCmd calls InstantiateImplementation only
                // under IsInlined (Monomorphization.cs:1584-1608). Otherwise the call site is
                // rewritten to an instantiated *procedure* with no implementation, and corral --
                // which verifies by inlining bodies, not by modular reasoning against contracts --
                // havocs the return value and reports a false "This assertion can fail".
                // corral inlines every implementation anyway, so mark them all inlined here.
                // The attribute is removed again below, so it cannot reach any later pass.
                // Recursive ones are marked too: Boogie 3.5.7 stack-overflowed on those, which
                // is fixed by the implInstantiationsInProgress guard in InlineCallCmd.
                foreach (var impl in init.TopLevelDeclarations.OfType<Implementation>()
                                         .Where(impl => impl.TypeParameters.Count > 0))
                    impl.AddAttribute("inline", Expr.Literal(1));

                var status = Monomorphizer.Monomorphize(BoogieUtil.BoogieOptions, init);
                if (status == MonomorphizableStatus.UnhandledPolymorphism)
                    throw new InvalidProg("Cannot monomorphize " + config.inputFile + ": unhandled polymorphism");
                if (status == MonomorphizableStatus.ExpandingTypeCycle)
                    throw new InvalidProg("Cannot monomorphize " + config.inputFile + ": expanding type cycle");

                foreach (var decl in init.TopLevelDeclarations)
                    decl.Attributes = BoogieUtil.removeAttr("inline", decl.Attributes);

                // Monomorphization rewrites in place; re-resolve so that no Decl from the
                // polymorphic program survives into the passes below
                init = BoogieUtil.ReResolveInMem(init);
            }

            // Get rid of lambdas: each one is replaced by a call to a freshly generated
            // map-valued function, plus an axiom defining that function. Boogie's own
            // ExecutionEngine does this too; corral never did, and Boogie2VCExprTranslator has no
            // case for LambdaExpr, so a lambda that survived to VC generation aborted the process
            // (a null deref in TranslateBinaryOperator, or Cce.UnreachableException in
            // VisitVariableSeq). This has to run after monomorphization: the lifted function does
            // not pick up type variables that occur only in the types of the captured variables,
            // so lifting a polymorphic lambda yields a function with an undeclared type parameter.
            if (BoogieUtil.BoogieOptions.ExpandLambdas)
            {
                LambdaHelper.ExpandLambdas(BoogieUtil.BoogieOptions, init);
            }

            // Add unique ids on calls. This has to run after monomorphization, which clones
            // implementations: clones would otherwise carry duplicates of the ids that
            // StratifiedInlining uses to identify call sites.
            var addIds = new AddUniqueCallIds();
            addIds.VisitProgram(init);

            // Gather the set of initially tracked variables
            initialTrackedVars = getTrackedVars(init, config);

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

        // Does the program compare two maps for (dis)equality anywhere? Keying on the
        // {:builtin "Map..."} functions instead would be both too narrow ("a == b" on [int]int
        // needs extensionality without mentioning any of them) and too wide (consuming a
        // MapImp fact pointwise does not).
        private static bool UsesMapEquality(Program program)
        {
            var detector = new MapEqualityDetector();
            detector.VisitProgram(program);
            return detector.found;
        }

        private class MapEqualityDetector : StandardVisitor
        {
            public bool found = false;

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (found) return node;

                if (node.Fun is BinaryOperator op
                    && (op.Op == BinaryOperator.Opcode.Eq || op.Op == BinaryOperator.Opcode.Neq))
                {
                    foreach (var arg in node.Args)
                    {
                        if (arg != null && arg.Type != null && containsMap(arg.Type, new HashSet<TypeCtorDecl>()))
                            found = true;
                    }
                }
                return base.VisitNAryExpr(node);
            }

            // Equality at a datatype counts as well: the prover reduces it to equality of the
            // constructor arguments, so comparing two Sets ("datatype Set<T> { Set(val: [T]bool) }",
            // base.bpl:151) still needs extensionality. Over-approximating here is free: the cost
            // of enabling extensionality on a program that does not need it is unmeasurable.
            private static bool containsMap(Microsoft.Boogie.Type type, HashSet<TypeCtorDecl> seen)
            {
                if (type.IsMap) return true;
                if (!type.IsCtor) return false;

                var decl = type.AsCtor.Decl as DatatypeTypeCtorDecl;
                if (decl == null || !seen.Add(decl)) return false;

                return decl.Constructors.Any(ctor =>
                    ctor.InParams.Any(field => containsMap(field.TypedIdent.Type, seen)));
            }
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
                if (!impl.IsSkipVerification(BoogieUtil.BoogieOptions))
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
                : base(program, null, -1, BoogieUtil.BoogieOptions)
            {
                this.declToAnnotations = new Dictionary<Declaration, QKeyValue>();
                // save annotation
                foreach (var decl in program.TopLevelDeclarations)
                {
                    declToAnnotations.Add(decl, decl.Attributes);
                    decl.Attributes = null;
                }
            }

            public void RunProcessImplementation(Program program, Implementation impl)
            {
                base.ProcessImplementation(program, impl);
            }

            new public static void ProcessImplementation(Program program, Implementation impl)
            {
                var ce = new CodeExprInliner(program);
                ce.RunProcessImplementation(program, impl);
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

        // Check program "inputProg" using variable abstraction
        public static bool checkAndRefine(PersistentCBAProgram prog, RefinementState refinementState, Action<ErrorTrace, string> printTrace, out ErrorTrace cexTrace)
        {
            cexTrace = null;
            var outcomeSuccess = true;
            var lightweight = true;
            GeneralRefinementScheme.useHierarchicalSearch = true;

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

                Log.WriteLine("Verifying program while tracking: {0}", refinementState.getVars().Variables.Print());

                // This records the transformation made when "curr" is
                // transformed to "counterexample"
                InsertionTrans tinfo = null;

                bool success =
                    CBADriver.checkProgram(ref prog, refinementState.getVars(), true, out counterexample, out tinfo, out cexTrace);

                if (success)
                {
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
                success = checkAndRefinePathFewPasses(counterexample, refinementState, out cexTrace);

                if (!success)
                {
                    // Generate cex in the original program
                    cexTrace = tinfo.mapBackTrace(cexTrace);
                    outcomeSuccess = false;
                    break;
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

            refinementState.Push();

            ConfigManager.beginRefinement();

            // Compute the new set of tracked variables to rule out this counterexample
            var refine = new GeneralRefinementScheme(new SequentialProgVerifier(), true, counterexample, refinementState);
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

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using cba.Util;

namespace cba
{
    public class Configs
    {
        public static void usage()
        {
            Console.WriteLine("Usage: corral fname [Flags]");
            Console.WriteLine();
            Console.WriteLine("-------------------------------------------------------------");
            Console.WriteLine("Flags (SMACK-compatible subset):");
            Console.WriteLine(" /k:int             \t Sets execution context bound");
            Console.WriteLine(" /main:str          \t Sets main procedure name");
            Console.WriteLine(" /recursionBound:int\t Set recursion depth bound");
            Console.WriteLine(" /trackAllVars      \t Track all shared variables.");
            Console.WriteLine(" /useArrayTheory    \t Use native array theory for z3.");
            Console.WriteLine(" /useProverEvaluate \t Use prover evaluate mode.");
            Console.WriteLine(" /timeLimit:n       \t Set Z3 timeout to n sec (default 500)");
            Console.WriteLine(" /cex:n             \t Max counterexamples");
            Console.WriteLine(" /maxStaticLoopBound:n\t Upper bound on minimum loop iterations");
            Console.WriteLine(" /tryCTrace         \t Generate C-style error trace");
            Console.WriteLine(" /noTraceOnDisk     \t Don't write trace files to disk");
            Console.WriteLine(" /printDataValues:n \t Print data values in trace");
            Console.WriteLine(" /v:n               \t Verbose mode level");
            Console.WriteLine(" /bopt:str          \t Pass-through options to Boogie");
            Console.WriteLine();
            Console.WriteLine("-------------------------------------------------------------");
        }

        public int contextBound { get; private set; }

        public string mainProcName { get; set; }

        public bool trackAllVars { get; private set; }

        public int recursionBound { get; private set; }

        public TraceFormat? genCTrace { get; private set; }
        public bool noTraceOnDisk { get; private set; }

        public string inputFile;

        public ArrayTheoryOptions arrayTheory { get; private set; }

        public int printData { get; set; }

        public int timeout { get; private set; }

        public string boogieOpts;

        public bool useProverEvaluate { get; private set; }

        public int maxStaticLoopBound { get; private set; }

        public int NumCex { get; private set; }

        public int verboseMode { get; private set; }

        public static Configs parseCommandLine(string[] args)
        {
            var inputFlags = FlagReader.read(args);

            // Go through flags and find the bpl file and
            // other flags

            string inputFile = null;

            List<string> flags = new List<string>();

            foreach (var str in inputFlags)
            {
                if (FlagReader.isFlag(str))
                {
                    flags.Add(str);
                    continue;
                }

                if (str.EndsWith(".bpl"))
                {
                    if (inputFile != null)
                    {
                        throw new UsageError(string.Format("Multiple input files given: {0} and {1}", inputFile, str));
                    }

                    inputFile = str;
                    continue;
                }

                throw new UsageError("Unknown argument: " + str);
            }

            if (inputFile == null)
            {
                throw new UsageError("Input file not given");
            }

            Configs config = new Configs();
            config.inputFile = inputFile;

            foreach (var flag in flags)
            {
                config.parseFlag(flag);
            }

            if (config.contextBound <= 0)
            {
                throw new UsageError("Context bound invalid");
            }

            if (config.recursionBound < 1)
            {
                Console.WriteLine("Warning: Using default recursion bound of 1");
                config.recursionBound = 1;
            }

            return config;
        }

        private Configs()
        {
            // Set defaults
            contextBound = 2;
            mainProcName = null;
            trackAllVars = false;

            genCTrace = null;
            noTraceOnDisk = false;
            inputFile = null;
            arrayTheory = ArrayTheoryOptions.WEAK;
            recursionBound = -1;
            timeout = 0;
            boogieOpts = " ";

            printData = 0;

            verboseMode = 0;
            maxStaticLoopBound = 0;

            useProverEvaluate = false;

            NumCex = 1;
        }


        private void parseFlag(string flag)
        {
            var sep = new char[1];
            sep[0] = ':';

            if (flag.StartsWith("/k:"))
            {
                var split = flag.Split(sep);
                contextBound = Int32.Parse(split[1]);
            }
            else if (flag.StartsWith("/main:"))
            {
                var split = flag.Split(sep);
                mainProcName = split[1];
            }
            else if (flag == "/trackAllVars")
            {
                trackAllVars = true;
            }
            else if (flag.StartsWith("/recursionBound:"))
            {
                var split = flag.Split(sep);
                recursionBound = Int32.Parse(split[1]);
            }
            else if (flag.StartsWith("/timeLimit:"))
            {
                var split = flag.Split(sep);
                timeout = Int32.Parse(split[1]);
            }
            else if (flag.StartsWith("/cex:"))
            {
                var split = flag.Split(sep);
                NumCex = Int32.Parse(split[1]);
            }
            else if (flag == "/useArrayTheory")
            {
                arrayTheory = ArrayTheoryOptions.STRONG;
            }
            else if (flag == "/useProverEvaluate")
            {
                useProverEvaluate = true;
            }
            else if (flag.StartsWith("/printDataValues:"))
            {
                var split = flag.Split(sep);
                printData = Int32.Parse(split[1]);
            }
            else if (flag.StartsWith("/maxStaticLoopBound:"))
            {
                var split = flag.Split(sep);
                maxStaticLoopBound = Int32.Parse(split[1]);
            }
            else if (flag == "/tryCTrace")
            {
                genCTrace = TraceFormat.ConcurrencyExplorer;
            }
            else if (flag == "/noTraceOnDisk")
            {
                noTraceOnDisk = true;
            }
            else if (flag.StartsWith("/v:"))
            {
                var split = flag.Split(sep);
                verboseMode = Int32.Parse(split[1]);
            }
            else if (flag.StartsWith("/bopt:"))
            {
                boogieOpts += " \"-" + flag.Substring("/bopt:".Length) + "\" ";
            }
            else
            {
                throw new UsageError("Invalid flag: " + flag);
            }
        }

    }

    public enum ArrayTheoryOptions { NONE, WEAK, STRONG };
}

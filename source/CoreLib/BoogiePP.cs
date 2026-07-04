using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace cba
{
    // This defines language-specific information.

    public class LanguageSemantics
    {
        // special variables ("alloc")
        public static HashSet<string> specialVars = new HashSet<string>(new string[] { "alloc" });

        public static readonly string tidName = "corral_tid";
        public static readonly string ThreadLocalAttr = "thread_local";

        // Name of the atomic_begin and atomic_end procedures
        public static string atomicBeginProcName()
        {
            return "corral_atomic_begin";
        }

        public static string atomicEndProcName()
        {
            return "corral_atomic_end";
        }

        // The procedure that returns the current thread ID
        public static string getThreadIDName()
        {
            return "corral_getThreadID";
        }

        // The procedure that returns the child thread ID
        public static string getChildThreadIDName()
        {
            return "corral_getChildThreadID";
        }

        // Name of the "is_reachable" procedure
        public static string assertNotReachableName()
        {
            return "corral_assert_not_reachable";
        }

        // Is this global variable potentially shared by threads?
        // (If so, CBA instruments this variable)
        // This is to give special treatment to variables like alloc
        public static bool isShared(string varName)
        {
            if (specialVars.Contains(varName)) return false;
            return true;
        }

        public static void print()
        {
            Console.WriteLine("Begin atomic block: \"call {0}();\"", atomicBeginProcName());
            Console.WriteLine("End atomic block  : \"call {0}();\"", atomicEndProcName());
            Console.WriteLine("Get thread id     : \"call n := {0}();\"", getThreadIDName());
            Console.WriteLine("Target            : \"call {0}();\"", assertNotReachableName());
        }

    }

}

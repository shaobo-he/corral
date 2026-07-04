using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using cba.Util;

namespace cba
{
    public class EntrypointScanner : StandardVisitor
    {
        List<string> entrypoints;

        private EntrypointScanner()
        {
            this.entrypoints = new List<string>();
        }
        public static List<string> FindEntrypoint(Program p)
        {
            var scanner = new EntrypointScanner();
            scanner.Visit(p);
            return scanner.entrypoints;
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            if (QKeyValue.FindBoolAttribute(node.Attributes, "entrypoint"))
                entrypoints.Add(node.Name);
            return base.VisitProcedure(node);
        }
    }

}

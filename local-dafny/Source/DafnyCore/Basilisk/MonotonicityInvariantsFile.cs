using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MonotonicityInvariantsFile {

    // List of invariants
    private List<MonotonicityInvariant> monotonicityInvariants;

    // Constructor
    public MonotonicityInvariantsFile()
    {
      monotonicityInvariants = new List<MonotonicityInvariant>{};
    }

    public void AddInvariant(MonotonicityInvariant mi) {
      monotonicityInvariants.Add(mi);
    }

    public List<MonotonicityInvariant> GetInvariants() {
      return monotonicityInvariants;
    }
  } // end class MonotonicityInvariantsFile
}
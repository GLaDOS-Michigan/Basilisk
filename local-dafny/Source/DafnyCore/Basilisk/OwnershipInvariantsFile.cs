using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny
{
public class OwnershipInvariantsFile {

  private IndDatatypeDecl hosts;  // datatype Hosts in DistributedSystem module

  // Constructor
  public OwnershipInvariantsFile()
  {}

  public void AddHosts(IndDatatypeDecl hosts) {
    Debug.Assert(this.hosts == null, "Hosts already non-null!");
    this.hosts = hosts;
  }

  public DatatypeDecl GetHosts() {
    Debug.Assert(hosts != null, "Variables is null!");
    return hosts;
  }

  // Extract a mapping of HostModulue -> field name in System.Variables
  public Dictionary<string, string> ExtractHosts() {
    Debug.Assert(hosts != null, "Variables is null!");
    var res = new Dictionary<string, string>();
    foreach (var formal in hosts.GroundingCtor.Formals) {
      int startIndex = formal.DafnyName.IndexOf("seq<") + "seq<".Length;
      int endIndex = formal.DafnyName.IndexOf(">", startIndex);
      var substring = formal.DafnyName.Substring(startIndex, endIndex - startIndex);
      var hostModule = substring.Split(".")[0];
      var field = formal.Name;
      res.Add(hostModule, field);
    }
    return res;
  }
} // end class OwnershipInvariantsFile
}
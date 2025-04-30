using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class DistributedSystemFile {
  private List<string> hostImports;  // host modules to import
  private IndDatatypeDecl constants;
  private IndDatatypeDecl variables;
  private Function initRelation;

  // Constructor
  public DistributedSystemFile()
  {
    hostImports = new List<string>();
  }

  public void AddHostImport(string moduleName) {
    hostImports.Add(moduleName);
  }

   public List<string> GetHostImports() {
    return hostImports;
  }

  public void AddConstants(IndDatatypeDecl constants) {
    Debug.Assert(this.constants == null, "Constants already non-null!");
    this.constants = constants;
  }

  public DatatypeDecl GetConstants() {
    Debug.Assert(constants != null, "Constants is null!");
    return constants;
  }

  public void AddVariables(IndDatatypeDecl variables) {
    Debug.Assert(this.variables == null, "Variables already non-null!");
    this.variables = variables;
  }

  public DatatypeDecl GetVariables() {
    Debug.Assert(variables != null, "Variables is null!");
    return variables;
  }

  // Extract a mapping of HostModulue -> field name in System.Variables
  public Dictionary<string, string> ExtractHosts() {
    Debug.Assert(variables != null, "Variables is null!");
    var res = new Dictionary<string, string>();
    foreach (var formal in variables.GroundingCtor.Formals) {
      int startIndex = formal.DafnyName.IndexOf("seq<") + "seq<".Length;
      int endIndex = formal.DafnyName.IndexOf(">", startIndex);
      var substring = formal.DafnyName.Substring(startIndex, endIndex - startIndex);
      var hostModule = substring.Split(".")[0];
      var field = formal.Name;
      res.Add(hostModule, field);
    }
    return res;
  }

  public void AddInitRelation(Function initRelation) {
    Debug.Assert(this.initRelation == null, "Init already non-null!");
    this.initRelation = initRelation;
  }

  public Function GetInitRelation() {
    Debug.Assert(initRelation != null, "Init is null!");
    return initRelation;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny
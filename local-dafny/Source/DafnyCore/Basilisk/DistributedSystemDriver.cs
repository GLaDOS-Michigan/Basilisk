using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class GenAsyncDriver {

  private readonly DafnyOptions options;
  private readonly Program program;
  private DistributedSystemFile dsFile;

  // Constructor
  public GenAsyncDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    dsFile = new DistributedSystemFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Generating asynchronous distributed system for {0}\n", program.FullName));
    var systemModule = GetModule("System");

    // Find imports, datatype Constants, datatype Variables
    IndDatatypeDecl variablesDecl = null;
    foreach (var decl in systemModule.TopLevelDecls.ToList()) {
      if (decl.Name.Contains("Host")) {
        dsFile.AddHostImport(decl.Name);
      } else if (decl.Name.Equals("Constants")) {
        dsFile.AddConstants((IndDatatypeDecl) decl);
      } else if (decl.Name.Equals("Variables")) {
        dsFile.AddVariables((IndDatatypeDecl) decl);
        variablesDecl = (IndDatatypeDecl) decl; // store for later use
      }
    }
    Debug.Assert(variablesDecl != null, "variablesDecl should not be null");

    // Find predicate Init
    foreach (var func in systemModule.DefaultClass.Members.Where(x => x.Name.Equals("Init"))) {
      dsFile.AddInitRelation((Function) func);
    }
  } // end method Resolve()

  // Returns the Dafny module with the given name
  private ModuleDefinition GetModule(string moduleName) {
    ModuleDefinition res = null;
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Equals(moduleName)) {
        res = moduleDef;
      }
    }
    Debug.Assert(res != null, String.Format("Module {0} not found ", moduleName));
    return res;
  } 

  public void WriteToFile() {
    string dsString = DistributedSystemPrinter.PrintDistributedSystem(dsFile, options, program.FullName);
    string dsOutputFullname = Path.GetDirectoryName(program.FullName) + "/distributedSystemAutogen.dfy";
    Console.WriteLine(string.Format("Writing distributed system to {0}", dsOutputFullname));
    File.WriteAllText(dsOutputFullname, dsString);
  }
}  // end class GenAsyncDriver
} // end namespace Microsoft.Dafny
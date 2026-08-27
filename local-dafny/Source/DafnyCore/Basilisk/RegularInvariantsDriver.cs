using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.Intrinsics.X86;
using System.Text.Json;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny
{
public class RegularInvariantsDriver {

  public DafnyOptions options;
  public Program program;
  public MessageInvariantsFile msgInvFile;
  public MonotonicityInvariantsFile monoInvFile;
  public OwnershipInvariantsFile ownerInvFile;
  public Dictionary<String, HostFootprint> footprintMap;

  // Constructor
  public RegularInvariantsDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
    monoInvFile = new MonotonicityInvariantsFile();
    ownerInvFile = new OwnershipInvariantsFile();
    footprintMap = new Dictionary<String, HostFootprint>();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Resolving invariants for {0}\n", program.FullName));

    // Find distributedSystem.Hosts
    DatatypeDecl dsHosts = null;
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllTypesWithMembers(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.FullDafnyName.Equals("DistributedSystem.Hosts")) {
          dsHosts = (DatatypeDecl) topLevelDecl;
          break;
        }
      }
    }
    Debug.Assert(dsHosts != null, "dsHosts should not be null");

    if (options.genFootprint){
      generateFootprint(program);
    }
    if (options.msgMonoInvs) {
      ResolveMonotonicityInvariants(dsHosts, program);
      ResolveSendInvariants(dsHosts, program);
      ResolveReceiveInvariants(dsHosts, program);
    }
    if (options.ownershipInvs) {
      ResolveOwnershipInvariants();
    }
  } // end method Resolve()

  private void ResolveOwnershipInvariants() {
    var systemModule = GetModule(program, "DistributedSystem");

    // Find datatype Hosts
    IndDatatypeDecl hostsDecl = null;
    foreach (var decl in systemModule.TopLevelDecls.ToList()) {
      if (decl.Name.Equals("Hosts")) {
        ownerInvFile.AddHosts((IndDatatypeDecl) decl);
        hostsDecl = (IndDatatypeDecl) decl;
        break;
      }
    }
    Debug.Assert(hostsDecl != null, "hostsDecl should not be null");
  }

  private void ResolveMonotonicityInvariants(DatatypeDecl dsHosts, Program program) {
    foreach (var kvp in program.ModuleSigs) {
      var module = kvp.Value.ModuleDef;
      if (module.DafnyName.Contains("Host")) {

        // Find Variable type definition
        foreach (var decl in module.SourceDecls) {
          if (decl.Name.Equals("Variables")) {
            var monoInvs = MonotonicityInvariant.FromVariableDecl((DatatypeDecl) decl, dsHosts);
            foreach (var mi in monoInvs) {
              monoInvFile.AddInvariant(mi);
            }
            break;
          }
        }
      }
    }
  }

  public static bool isTransition(Function func){
    if(func.Name == "Next" || func.Name == "NextStep"){
      return false;
    }
    foreach(var param in func.Formals){
      if (param.DisplayName == "v'"){
        return true;
      }
    }
    return false;
  }

  private string responseType(Expression expr){
    if (expr is BinaryExpr binaryExpr){
      String type1 = responseType(binaryExpr.E0);
      return type1 == "null" ? responseType(binaryExpr.E1) : type1;
    }
    else if(expr is LetExpr letExpr){
      return responseType(letExpr.Body);
    }
    else if(expr is ExprDotName checkExpr && checkExpr.Lhs is NameSegment nameSegment
      && nameSegment.Name == "inMsg"){
      return checkExpr.SuffixName.Substring(0, checkExpr.SuffixName.Length - 1);
    }
    return "null";
  }

  private bool isMonotonicDatatype(DatatypeDecl datatype){
    return datatype != null && datatype.Name.StartsWith("Monotonic")
      && datatype.ConstructorsByName.Count == 1 && datatype.TypeArgs.Count == 0;
  }
  private void getUpdatedVariables(DatatypeUpdateExpr updateExpr, List<String> updatedVariablesName, StepFootprint stepFootprint, String prefix){
    foreach(Tuple<IToken, string, Expression> update in updateExpr.Updates){
      if (update.Item3 is DatatypeUpdateExpr subUpdateExpr){
        getUpdatedVariables(subUpdateExpr, updatedVariablesName, stepFootprint, prefix + update.Item2 + ".");
      }
      else{
        var datatype = update.Item3.Type.AsDatatype;
        if (isMonotonicDatatype(datatype)){
          foreach(var formal in datatype.Ctors[0].Formals){
            var updatedVariable = prefix + update.Item2 + "." + formal.Name;
            if (!updatedVariablesName.Contains(updatedVariable)){
              updatedVariablesName.Add(updatedVariable);
              stepFootprint.Fields.Add(new BasiliskField(updatedVariable, formal.Type.ToString()));
            }
          }
        }
        else{
          var updatedVariable = prefix + update.Item2;
          if (!updatedVariablesName.Contains(updatedVariable)){
            updatedVariablesName.Add(updatedVariable);
            stepFootprint.Fields.Add(new BasiliskField(update.Item2, update.Item3.Type.ToString()));
          }
        }

      }
    }
  }
  private void findUpdatedVariables(Expression expr, List<String> updatedVariablesName, StepFootprint stepFootprint){
    if (expr is BinaryExpr binaryExpr){
      findUpdatedVariables(binaryExpr.E0, updatedVariablesName, stepFootprint);
      findUpdatedVariables(binaryExpr.E1, updatedVariablesName, stepFootprint);
    }
    else if(expr is LetExpr letExpr){
      findUpdatedVariables(letExpr.Body, updatedVariablesName, stepFootprint);
    }
    else if (expr is ITEExpr ifThenElseExpr){
      findUpdatedVariables(ifThenElseExpr.Thn, updatedVariablesName, stepFootprint);
      findUpdatedVariables(ifThenElseExpr.Els, updatedVariablesName, stepFootprint);
    }
    else if(expr is DatatypeUpdateExpr updateExpr){
      getUpdatedVariables(updateExpr, updatedVariablesName, stepFootprint, "");
    }
    return;

  }
  private void updateFootprint(Function func, HostFootprint hostFootprint){
    var responseMsg = responseType(func.Body);
    var updatedVariablesName = new List<String>();
    var stepFootprint = new StepFootprint(func.Name);
    findUpdatedVariables(func.Body, updatedVariablesName, stepFootprint);
    if(stepFootprint.Fields.Count != 0){
      Dictionary<string, StepFootprint> stepFootprints = hostFootprint.MsgFootprints.GetOrCreate(responseMsg, () => new Dictionary<string, StepFootprint>());
      stepFootprints.Add(func.Name, stepFootprint);
    }

    return;
  }
  private void generateFootprint(Program program) {
    // Find Send Predicate definitions
    foreach (var kvp in program.ModuleSigs) {
      HostFootprint hostFootprint = new HostFootprint();
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        var name = topLevelDecl.Name;
        // var isSendPredicate = (name.StartsWith("Receive") && name.Contains("Send"));

        if (topLevelDecl.FullDafnyName.Contains("Host") && isTransition(topLevelDecl)) {  // identifying marker for Send Predicate
          updateFootprint(topLevelDecl, hostFootprint);
        }
      }
      if (hostFootprint.MsgFootprints.Count > 0){
        footprintMap.Add(kvp.Key.Name, hostFootprint);
      }
    }
  }

  private void ResolveSendInvariants(DatatypeDecl dsHosts, Program program) {
    // Find Send Predicate definitions
    var sendPredicateDefs = new List<Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        var name = topLevelDecl.Name;
        var isSendPredicate = name.StartsWith("Send") || (name.StartsWith("Receive") && name.Contains("Send"));
        if (isSendPredicate && !topLevelDecl.FullDafnyName.StartsWith("Types.")) {  // identifying marker for Send Predicate
          sendPredicateDefs.Add(topLevelDecl);
        }
      }
    }

    // Create SendInvariant objects
    foreach (var sp in sendPredicateDefs) {
      var sendInv = SendInvariant.FromFunction(sp, dsHosts);
      msgInvFile.AddSendInvariant(sendInv);
    }
  }

  private void ResolveReceiveInvariants(DatatypeDecl dsHosts, Program program) {
    // One top level receive invariant for each host
    var recvInvList = ReceiveInvariant.FromHost(dsHosts, program);
    foreach (var recvInv in recvInvList) {
      msgInvFile.AddReceiveInvariant(recvInv);
    }

    // Receive skolemization objects, by reading json
    var footprintPath = Path.GetDirectoryName(program.FullName) + "/footprintsAutogen.json";
    string rawJson = File.ReadAllText(footprintPath);
    var parsedJson = JsonSerializer.Deserialize<Dictionary<string, HostFootprint>>(rawJson);
    var recvSkolemizationsList = ReceiveSkolemization.FromFootprints(dsHosts, parsedJson);
    foreach (var recvSkolem in recvSkolemizationsList) {
      msgInvFile.AddReceiveSkolemization(recvSkolem);
    }
    var customSkolemizationList = ReceiveSkolemization.FromCustomInvariants(dsHosts, program);
    foreach (var customSkolem in customSkolemizationList) {
      msgInvFile.AddReceiveSkolemization(customSkolem);
    }
    if (customSkolemizationList.Count > 0) {
      msgInvFile.IncludeCustomInvariants = true;
    }
  }

  private Dictionary<string, HostHint> ParseHintsJson(Dictionary<string, object> data) {
    var result = new Dictionary<string, HostHint>();  // map from host type to HostHint

    foreach (var kvp in data) {
      Debug.Assert(kvp.Value is JsonElement);
      var msgToFieldsElement = (JsonElement)kvp.Value;
      Debug.Assert(msgToFieldsElement.ValueKind == JsonValueKind.Object);

      var hostType = kvp.Key;
      var hostHint = new HostHint();

      var msgToFields = JsonSerializer.Deserialize<Dictionary<string, JsonElement>>(msgToFieldsElement.GetRawText());

      foreach (var mf in msgToFields) {
        var msgType = Regex.Replace(mf.Key, @"^\d+:\s*", ""); // strip numbering prefix
        if (!hostHint.HostHints.ContainsKey(msgType)) {
          hostHint.HostHints.Add(msgType, new List<List<BasiliskField>>());
        }
        var fieldsList = new List<BasiliskField>();
        foreach (var f in mf.Value.EnumerateArray()) {
          var fieldName = f.ToString();

          var hostModule = GetModule(program, hostType);

          // Find datatype Variables
          TopLevelDecl variablesDecl = null;
          foreach (var decl in hostModule.TopLevelDecls.ToList()) {
            if (decl.Name.Equals("Variables")) {
              variablesDecl = decl;
              break;
            }
          }
          var fieldType = GetTypeOfField((DatatypeDecl) variablesDecl, fieldName);
          fieldsList.Add(new BasiliskField(fieldName, fieldType));
        }
        hostHint.HostHints[msgType].Add(fieldsList);
      }
      result[hostType] = hostHint;
    }
    return result;
  }

  public string GetTypeOfField(DatatypeDecl decl, string fieldName) {
    Debug.Assert(decl.Ctors.Count == 1);

    var parts = fieldName.Split('.');

    var ctor = decl.Ctors[0];
    foreach (var formal in ctor.Formals) {
      if (formal.Name.Equals(parts[0])) {
        if (parts.Length == 1) {
          // Base Case
          return formal.Type.ToString();
        } else {
          // Recursive Case
          return GetTypeOfField(formal.Type.AsDatatype, string.Join(".", parts.Skip(1)));
        }
      }
    }
    Debug.Assert(false, "Cannot find field");
    return "dummyType";
  }

  // Returns the Dafny module with the given name
  public static ModuleDefinition GetModule(Program program, string moduleName) {
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
    if (options.genFootprint) {
      string footprintJsonString = RegularInvPrinter.PrintFootprintJson(footprintMap);
      string footprintOutputFullName = Path.GetDirectoryName(program.FullName) + "/footprintsAutogen.json";
      Console.WriteLine(string.Format("Writing footprint to {0}", footprintOutputFullName));
      File.WriteAllText(footprintOutputFullName, footprintJsonString);
    }
    if (options.msgMonoInvs) {
      // Write monotonicity invariants
      string monoInvString = RegularInvPrinter.PrintMonotonicityInvariants(monoInvFile, program.FullName);
      string monoInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/monotonicityInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing monotonicity invariants to {0}", monoInvOutputFullname));
      File.WriteAllText(monoInvOutputFullname, monoInvString);

      // Write message invariants
      string msgInvString = RegularInvPrinter.PrintMessageInvariants(msgInvFile, program.FullName);
      string msgInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing message invariants to {0}", msgInvOutputFullname));
      File.WriteAllText(msgInvOutputFullname, msgInvString);
    }
    if (options.ownershipInvs) {
      // Write ownership invariants
      string ownerInvString = RegularInvPrinter.PrintOwnershipInvariants(ownerInvFile, program.FullName);
      string ownerInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/ownershipInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing ownership invariants to {0}", ownerInvOutputFullname));
      File.WriteAllText(ownerInvOutputFullname, ownerInvString);
    }
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny
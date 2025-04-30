using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.InteropServices;
using System.Security.Cryptography.X509Certificates;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis;


namespace Microsoft.Dafny
{
  public class ReceiveInvariant {

    private bool opaque;
    private string hostModule;  // name of the module this function belongs
    private string hostField;   // which field in distributedSystem.Hosts?

    public ReceiveInvariant(string hostModule, string hostField) {
      this.opaque = true;
      this.hostModule = hostModule;
      this.hostField = hostField;
    }

    public static List<ReceiveInvariant> FromHost(DatatypeDecl dsHosts) {
      var res = new List<ReceiveInvariant>();

      foreach (var formal in dsHosts.Ctors[0].Formals) {
        var name = formal.DafnyName;
        if (name.Contains("Host.Variables")) {
        
          // Find the index of the first '<'
          int startIndex = name.IndexOf('<') + 1;
          // Find the index of the first '.' after the '<'
          int endIndex = name.IndexOf('.', startIndex);
          // Extract the substring between '<' and '.'
          string hostModule = name.Substring(startIndex, endIndex - startIndex);
          string hostField = name.Substring(0, name.IndexOf(":"));

          var recvInv = new ReceiveInvariant(hostModule, hostField);
          Console.WriteLine(recvInv);
          res.Add(recvInv);
        }
      }
      return res;
    }

    public bool Opaque {
      get { return opaque; }
    }

    public string GetPredicateName() {
      return string.Format("{0}ReceiveValidity", hostModule);
    }

    public string ToPredicate() {
      return string.Format(RegularInvPrinter.GetFromTemplate("HostReceiveValidity", 0), hostModule, hostField);
    }

    public string GetLemmaName() {
      return string.Format("InvNext{0}ReceiveValidity", hostModule);
    }

    public string ToLemma() {
      var res = "";
      res += string.Format(RegularInvPrinter.GetFromTemplate("HostReceiveSkolemization", 0), hostModule, hostField, GetPredicateName());
      res += "\n";
      res += string.Format(RegularInvPrinter.GetFromTemplate("InvNextHostReceiveValidity", 0), hostModule, hostField);
      return res;
    }

    public override string ToString() {
      return string.Format("Receive invariant for [{0}], in DistributedSystem.hosts.[{1}]\n", hostModule, hostField);
    }
  } // end class ReceiveInvariant

  public class ReceiveSkolemization {
    public const string NullMsg = "null";

    private int Id            {get; set;}
    private bool IsHint       { get; }      // is this from a user hint?
    private string HostModule { get; }      // name of the module this function belongs
    private string HostField  { get; }      // which field in distributedSystem.Hosts?
    private bool IsNullMsg    { get; }      // is this for a null message
    private string Step       { get; }      // name of the transition, could be a CSV if this is an intra-message intersection skolemization
    private string WitnessName { get; }     // name of the witness for custom invariants
    private List<BasiliskField> Fields { get; }     // host fields that go into witness condition

    public ReceiveSkolemization(bool isHint, string hostModule, string hostField, bool isNullMsg, string step, List<BasiliskField> fields) {
      IsHint = isHint;
      HostModule = hostModule;
      HostField = hostField;
      IsNullMsg = isNullMsg;
      Step = step;  // Step could be a CSV if this is an intra-message intersection skolemization
      Fields = fields;
    }

    public ReceiveSkolemization(bool isHint, string hostModule, string hostField, bool isNullMsg, string step, List<BasiliskField> fields, string witnessName, int id) {
      IsHint = isHint;
      HostModule = hostModule;
      HostField = hostField;
      IsNullMsg = isNullMsg;
      Step = step;  // Step could be a CSV if this is an intra-message intersection skolemization
      Fields = fields;
      WitnessName = witnessName;
      Id = id;
    }

    public static Dictionary<string, string> GetHostTransitionsMap(DatatypeDecl dsHosts, Program program){
      var functionNameMap = new Dictionary<string, string>();
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
          var name = topLevelDecl.Name;
          if (topLevelDecl.FullDafnyName.Contains("Host") && RegularInvariantsDriver.isTransition(topLevelDecl)) {  // identifying marker for Send Predicate
            functionNameMap.Add(name, kvp.Key.Name);
          }
        }
      }
      return functionNameMap;
    }
    private static string GetHostField(string hostModule, DatatypeDecl dsHosts){
      var hostField = "";
      foreach (var formal in dsHosts.Ctors[0].Formals) {
        var name = formal.DafnyName;
        if (name.Contains("Host.Variables")) {
          // Find the index of the first '<'
          int startIndex = name.IndexOf('<') + 1;
          // Find the index of the first '.' after the '<'
          int endIndex = name.IndexOf('.', startIndex);
          // Extract the substring between '<' and '.'
          string mod = name.Substring(startIndex, endIndex - startIndex);
          if (mod == hostModule) {
            hostField = name.Substring(0, name.IndexOf(":"));  // populate hostField
            break;
          }
        }
      }
      return hostField;
    }
    public static List<ReceiveSkolemization> FromCustomInvariants(DatatypeDecl dsHosts, Program program){
      var res = new List<ReceiveSkolemization>();
      var functionNameMap = GetHostTransitionsMap(dsHosts, program);
      foreach (var kvp in program.ModuleSigs) {
        if (kvp.Key.Name != "CustomMessageInvariants"){
          continue;
        }
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
          var name = topLevelDecl.Name;
          var step = "";
          var hostModule = "";
          foreach (var functionKvp in functionNameMap){
            if(name.Contains(functionKvp.Key)){
              if (step != "") {
                step += ",";
              }
              if (hostModule == "") {
                hostModule = functionKvp.Value;
              }
              step += functionKvp.Key;
            }
          }
          string hostField = GetHostField(hostModule, dsHosts);
          Debug.Assert(!string.IsNullOrEmpty(hostField));
          var id = int.Parse(new string(name.SkipWhile(c=>!char.IsDigit(c))
                         .TakeWhile(c=>char.IsDigit(c))
                         .ToArray()));
          
          var fields = new List<BasiliskField>();
          foreach (var formal in topLevelDecl.Formals) {
            if (formal.Name == "c" || formal.Name == "v" || formal.Name == "i" || formal.Name == "idx") {
              continue;
            }
            var field = new BasiliskField(formal.Name, formal.Type.ToString());
            fields.Add(field);
          }
          var isNullMsg = !name.Contains("Receive");
          var recvSkolem = new ReceiveSkolemization(true, hostModule, hostField, isNullMsg, step, fields, name, id);
          res.Add(recvSkolem);
        }
      }
      return res;
    }
    public static List<ReceiveSkolemization> FromFootprints(DatatypeDecl dsHosts, Dictionary<string, HostFootprint> footprints) {
      var res = new List<ReceiveSkolemization>();
      foreach (var kvp in footprints) {
        string hostModule = kvp.Key;
        var hostFootprint = kvp.Value;

        // Extract hostField
        string hostField = GetHostField(hostModule, dsHosts);
        Debug.Assert(!string.IsNullOrEmpty(hostField));
        res.AddRange(ParseHostFootprint(hostModule, hostField, hostFootprint));
      }
      return res;
    }

    static Dictionary<string, HashSet<string>> GetAllIntersections(Dictionary<string, HashSet<string>> sets) {
      var result = new Dictionary<string, HashSet<string>>();

      // Get all subsets of keys to generate intersections
      var keys = sets.Keys.ToList();
      int n = keys.Count;

      // Iterate over all non-empty subsets of keys
      for (int i = 1; i < (1 << n); i++) {
        var subsetKeys = new List<string>();
        HashSet<string> intersection = null;

        for (int j = 0; j < n; j++) {
          if ((i & (1 << j)) != 0) {
            var key = keys[j];
            subsetKeys.Add(key);
            if (intersection == null) {
              // Start with the set of the first key in the subset
              intersection = new HashSet<string>(sets[key]);
            } else {
              // Intersect with the next set in the subset
              intersection.IntersectWith(sets[key]);
            }
          }
        }
        if (intersection != null && intersection.Count > 0) {
          string subsetKey = string.Join(",", subsetKeys);
          result[subsetKey] = intersection;
        }
      }
      return result;
    }

    // Heavy-duty lifting here
    private static List<ReceiveSkolemization> ParseHostFootprint(string hostModule, string hostField, HostFootprint hostFootprint) {

      var fieldsMap = new Dictionary<string, BasiliskField>(); // map of field name to their BasiliskField object 
      var stepMap = new Dictionary<string, HashSet<string>>(); // map of step names to list of field names

      // Populate fieldsMap and stepMap
      foreach (var msgFootprint in hostFootprint.MsgFootprints) {
        var msgType = msgFootprint.Key;
        foreach (var stepFootprint in msgFootprint.Value) {
          var step = stepFootprint.Step;

          // Special naming for null-recv steps
          if (msgType.Equals(NullMsg)) {
            step = "Null" + step;
          }

          stepMap.Add(step, new HashSet<string>());
          foreach (var field in stepFootprint.Fields) {
            if (!fieldsMap.ContainsKey(field.Name)) {
              fieldsMap.Add(field.Name, field);
            }
            stepMap[step].Add(field.Name);
          }
        }
      }

      var intersections = GetAllIntersections(stepMap);

      // Remove any fields that appear in a stronger intersection
      foreach (var kvp1 in intersections) {
        foreach (var kvp2 in intersections) {
          var steps1 = new HashSet<string>(kvp1.Key.Split(',').Select(s => s.Trim()));
          var steps2 = new HashSet<string>(kvp2.Key.Split(',').Select(s => s.Trim()));
          if (steps1.IsSubsetOf(steps2) && !steps1.SetEquals(steps2)) {
            foreach (var field in fieldsMap.Keys) {
              if (kvp1.Value.Contains(field) && kvp2.Value.Contains(field)) {
                kvp1.Value.Remove(field);
              }
            }
          }
        }
      }

      // Generate final output
      var res = new List<ReceiveSkolemization>();
      foreach (var kvp in intersections) {
        if (kvp.Value.Count == 0) {
          continue;
        }
        var stepsSet = new HashSet<string>(kvp.Key.Split(',').Select(s => s.Trim()));
        if (stepsSet.Count > 1 && stepsSet.Any(s => s.Contains("Null"))) {
          Console.Write("Intersection with Null-receive currently not supported");
          continue;
          // Debug.Assert(false, "Intersection with Null-receive not supported");
        }

        var steps = kvp.Key;
        var fields = new List<BasiliskField>();
        foreach (var fieldName in kvp.Value) {
          fields.Add(fieldsMap[fieldName]);
        }

        if (steps.StartsWith("Null")) {
          steps = steps.Substring("Null".Length);
          var recvSkolem = new ReceiveSkolemization(false, hostModule, hostField, true, steps, fields);
          res.Add(recvSkolem);
        } else {
          var recvSkolem = new ReceiveSkolemization(false, hostModule, hostField, false, steps, fields);
          res.Add(recvSkolem);
        }
      }
      return res;
    }

    public string ToSkolemization() {
      var res = WitnessCondition();
      res += "\n";

      var isRecvSend = Step.Contains("Receive") && Step.Contains("Send");  // is this a receive-and-send step?

      if (isRecvSend) {
        res += string.Format(
          RegularInvPrinter.GetFromTemplate("ReceiveSkolemization2", 0), 
          SkolemizationName(), 
          SkolemizationFormals(), 
          HostModule,
          HostField,
          WitnessConditionName(),
          WitnessArgs(),
          EnsuresStep()
        );
      } else if (IsNullMsg) {
        res += string.Format(
          RegularInvPrinter.GetFromTemplate("ReceiveSkolemizationNull", 0), 
          SkolemizationName(), 
          SkolemizationFormals(), 
          HostModule,
          HostField,
          WitnessConditionName(),
          WitnessArgs()
        );
      } else {
        res += string.Format(
          RegularInvPrinter.GetFromTemplate("ReceiveSkolemization", 0), 
          SkolemizationName(), 
          SkolemizationFormals(), 
          HostModule,
          HostField,
          WitnessConditionName(),
          WitnessArgs(),
          EnsuresStep()
        );
      }
      return res;
    }

    private string SkolemizationName() {
      var name = String.Concat(Step.Where(c => c != ',' && !Char.IsWhiteSpace(c)));
      var res = string.Format("{0}StepSkolemization", name);
      if (IsHint) {
        res = "Custom" + Id + res;
      }
      return res;
    }

    private string WitnessConditionName() {
      if (IsHint) {
        Debug.Assert(!string.IsNullOrEmpty(WitnessName));
        return WitnessName;
      }
      var name = String.Concat(Step.Where(c => c != ',' && !Char.IsWhiteSpace(c)));
      var res = string.Format("{0}WitnessCondition", name);
      if (IsHint) {
        res = "Custom" + Id + res;
      }
      return res;
    }

    private string EnsuresStep() {
      var steps = Step.Split(',').Select(s => s.Trim()).ToList();
      var isRecvSend = steps[0].Contains("Receive") && Step.Contains("Send");  // is this a receive-and-send step?
      var res = new List<string>();
      foreach (var step in steps) {
        if (isRecvSend) {
          res.Add(
            string.Format("{0}.{1}(c.{2}[idx], v.History(j).{2}[idx], v.History(j+1).{2}[idx], inMsg, outMsg)",
            HostModule, step, HostField)
          );
        } else {
          res.Add(
            string.Format("{0}.{1}(c.{2}[idx], v.History(j).{2}[idx], v.History(j+1).{2}[idx], inMsg)",
            HostModule, step, HostField)
          );
        }
      }
      return string.Join(" || ", res);
    }

    // Additional arguments beyond the mandatory "c: Constants, v: Variables, i: nat, idx: int"
    private string SkolemizationFormals() {
      var res = new List<string>();
      var count = 1;
      foreach (var f in Fields) {
        var parsedField = FormalsForType(f.Type, count);
        count = parsedField.nextCount;
        res.Add(parsedField.res);
      }
      return string.Join(", ", res);
    }

    private (string res, int nextCount) FormalsForType(string type, int startingCount) {
      var count = startingCount;
      if (type.StartsWith("set<") || type.StartsWith("MonotonicSet<")) {
        // Base case: Dafny built-in set, or Basilisk built-in MonotonicSet
        int startIndex = type.IndexOf('<');
        int endIndex = type.LastIndexOf('>');
        string paramType = type.Substring(startIndex + 1, endIndex - startIndex - 1);
        return (string.Format("a{0}: {1}", count, paramType), count + 1);
      } else if (type.StartsWith("seq<")) {
        // Recursive case: Dafny built-in seq
        int startIndex = type.IndexOf('<');
        int endIndex = type.LastIndexOf('>');
        string paramType = type.Substring(startIndex + 1, endIndex - startIndex - 1);
        var suffix = FormalsForType(paramType, count + 1);
        return (string.Format("a{0}: {1}, {2}", count, "nat", suffix.res), suffix.nextCount);
      } else if (type.StartsWith("map<") || type.Contains("MonotonicMap<")) {
        // Recursive case: Dafny built-in map, or Basilisk built-in MonotonicMap
        int startIndex = type.IndexOf('<');
        int endIndex = type.LastIndexOf('>');
        string innerContent = type.Substring(startIndex + 1, endIndex - startIndex - 1);
        string[] parts = innerContent.Split(new[] { ',' }, 2);
        string typeA = parts[0].Trim();
        string typeB = parts[1].Trim();
        var suffix = FormalsForType(typeB, count + 1);
        return (string.Format("a{0}: {1}, {2}", count, typeA, suffix.res), suffix.nextCount);
      } else {
        // Base case
        return (string.Format("a{0}: {1}", count, type), count + 1);
      }
    }

    private string WitnessArgs() {
      var res = new List<string>();
      var count = 1;
      foreach (var f in Fields) {
        var witnessArgs = WitnessArgsForType(f.Type, count);
        count = witnessArgs.nextCount;
        res.Add(witnessArgs.res);
      }
      return string.Join(", ", res);
    }

    private (string res, int nextCount) WitnessArgsForType(string type, int count) {
      if (type.StartsWith("map<") || type.Contains("MonotonicMap<")) {
        // Recursive case: Dafny built-in map, or Basilisk built-in MonotonicMap
        int startIndex = type.IndexOf('<');
        int endIndex = type.LastIndexOf('>');
        string innerContent = type.Substring(startIndex + 1, endIndex - startIndex - 1);
        string[] parts = innerContent.Split(new[] { ',' }, 2);
        string typeB = parts[1].Trim();
        var suffix = WitnessArgsForType(typeB, count + 1);
        return (string.Format("a{0}, {1}", count, suffix.res), suffix.nextCount);
      } else if (type.StartsWith("seq<")) {
        // Recursive case: Dafny built-in seq
        int startIndex = type.IndexOf('<');
        int endIndex = type.LastIndexOf('>');
        string paramType = type.Substring(startIndex + 1, endIndex - startIndex - 1);
        var suffix = WitnessArgsForType(paramType, count + 1);
        return (string.Format("a{0}, {1}", count, suffix.res), suffix.nextCount);
      } else {
        // Base case
        return (string.Format("a{0}", count), count + 1);
      }
    }

    private string WitnessExpression() {
      var res = new List<string>();
      var count = 1;
      foreach (var f in Fields) {
        var witnessExpr = WitnessExpressionForType(f.Type, f.Name, count);
        count = witnessExpr.nextCount;
        res.Add(witnessExpr.res);
      }

      // Add non-init condition
      res.Add("(" + NonInitExpression() + ")");

      return "&& " + string.Join("\n  && ", res);
    }

    private (string res, int nextCount) WitnessExpressionForType(string type, string name, int count) {
      if (type.StartsWith("set<")) {
          // Dafny built-in set
          return (string.Format("a{0} in v.History(i).{1}[idx].{2}", count, HostField, name), count+1);
        } else if (type.StartsWith("MonotonicSet<")) {  
          // Basilisk built-in MonotonicSet
          return (string.Format("a{0} in v.History(i).{1}[idx].{2}.s", count, HostField, name), count+1);
        } else if (type.StartsWith("map<")) {
          // Recursive case: Dafny built-in map
          var key = string.Format("a{0}", count);
          int startIndex = type.IndexOf('<');
          int endIndex = type.LastIndexOf('>');
          string innerContent = type.Substring(startIndex + 1, endIndex - startIndex - 1);
          string[] parts = innerContent.Split(new[] { ',' }, 2);
          string typeB = parts[1].Trim();
          var nextName = string.Format("{0}[{1}]", name, key);
          var suffix = WitnessExpressionForType(typeB, nextName, count + 1);
          return (string.Format("{0} in v.History(i).{1}[idx].{2}\n  && {3}", key, HostField, name, suffix.res), suffix.nextCount);
        } else if (type.StartsWith("MonotonicMap<")) {
          // Recursive case: Basilisk built-in MonotonicMap
          var key = string.Format("a{0}", count);
          int startIndex = type.IndexOf('<');
          int endIndex = type.LastIndexOf('>');
          string innerContent = type.Substring(startIndex + 1, endIndex - startIndex - 1);
          string[] parts = innerContent.Split(new[] { ',' }, 2);
          string typeB = parts[1].Trim();
          var nextName = string.Format("{0}[{1}].m", name, key);
          var suffix = WitnessExpressionForType(typeB, nextName, count + 1);
          return (string.Format("{0} in v.History(i).{1}[idx].{2}.m\n  && {3}", key, HostField, name, suffix.res), suffix.nextCount);
        } else if (type.StartsWith("seq<")) {
          // Recursive case: Dafny built-in seq
          var key = string.Format("a{0}", count);
          int startIndex = type.IndexOf('<');
          int endIndex = type.LastIndexOf('>');
          string paramType = type.Substring(startIndex + 1, endIndex - startIndex - 1);
          var nextName = string.Format("{0}[{1}]", name, key);
          var suffix = WitnessExpressionForType(paramType, nextName, count + 1);
          return (string.Format("0 <= {0} < |v.History(i).{1}[idx].{2}|\n  && {3}", key, HostField, name, suffix.res), suffix.nextCount);
        } else {
          return (string.Format("a{0} == v.History(i).{1}[idx].{2}", count, HostField, name), count + 1);
        }
    }

    private string WitnessCondition() {
      if (IsHint){
        return "";
      }
      return string.Format(
        RegularInvPrinter.GetFromTemplate("StepWitnessCondition", 0), 
        WitnessConditionName(), 
        SkolemizationFormals(), 
        HostField, 
        WitnessExpression()
      );
    }

    // Expression asserting that footprint fields do not all hold their initial values
    private string NonInitExpression() {
      var res = new List<string>();
      foreach (var f in Fields) {
        res.Add(string.Format("v.History(i).{0}[idx].{1} != v.History(0).{0}[idx].{1}", HostField, f.Name));
      }
      return string.Join(" || ", res);
    }

    public override string ToString() {
      return string.Format("Receive skolemization for step [{0}.{1}] in module [{1}]", HostModule, Step);
    }
  }
}
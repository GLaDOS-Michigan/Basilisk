using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.VisualBasic;

namespace Microsoft.Dafny
{

  public class MonotonicityInvariant {

    private string name;      // base name, i.e. name of the monotonic variable
    private string typeName;  // name of the monotonic type
    private string module;    // name of the host module this was found
    private string variableField;  // which field in distributedSystem.Hosts?

    public MonotonicityInvariant(string name, string typeName, string module, string variableField) {
      this.name = name;
      this.typeName = typeName;
      this.module = module;
      this.variableField = variableField;
    }

    public static List<MonotonicityInvariant> FromVariableDecl(DatatypeDecl variableDecl, DatatypeDecl dsHosts) {
      // Extract module and msgType
      var module = ExtractInvariantModule(variableDecl);
      var res = new List<MonotonicityInvariant>();

      foreach (var formal in variableDecl.GetGroundingCtor().Formals) {
        var typeName = ExtractTypeName(formal);
        if (typeName.StartsWith("Monotonic")) {   
          // Found a monotonic type
          var name = formal.DisplayName;

          // extract field name in DistributedSystem.Hosts of type seq<[module].Variables>
          string variableField = null;
          foreach (var f in dsHosts.GetGroundingCtor().Formals) {
            if (f.DafnyName.Contains(string.Format("{0}.Variables", module))) {
              variableField = f.CompileName;
              break;
            }
          }
          Debug.Assert(variableField != null, "variableField should not be null");

          Console.WriteLine(string.Format("Found monotonic field [{0}: {1}] in module [{2}], in DistributedSystem.[Hosts.{3}]\n", name, typeName, module, variableField));

          var monoInv = new MonotonicityInvariant(name, typeName, module, variableField);
          res.Add(monoInv);
        }
      }
      return res;
    }
    
    // Get the Module in Module.Variables
    private static string ExtractInvariantModule(TopLevelDecl func) {
      return func.FullDafnyName.Substring(0, func.FullDafnyName.IndexOf('.'));
    }

        // Get the Module in Module.Variables
    private static string ExtractTypeName(Formal formal) {
      return formal.DafnyName.Split(":")[1].Trim();
    }

    public string GetName() {
      return this.name;
    }

    private string GetNameCapitalized() {
      return char.ToUpper(name[0]) + name.Substring(1);
    }

    public string GetPredicateName() {
      return string.Format("{0}{1}Monotonic", module, GetNameCapitalized());
    }

    public string GetWitnessPredicateName() {
      return string.Format("{0}{1}ExistsWitness", module, GetNameCapitalized());
    }

    public string GetLemmaName() {
      return string.Format("InvNext{0}{1}Monotonic", module, GetNameCapitalized());
    }

    public string GetWitnessLemmaName() {
      return string.Format("InvNext{0}{1}ExistsWitness", module, GetNameCapitalized());
    }

    public string GetSkolemizationName() {
      return string.Format("{0}{1}Skolemization", module, GetNameCapitalized());
    }

    public string ToPredicate() {
      var res = string.Format("ghost predicate {0}(c: Constants, v: Variables)\n", GetPredicateName());
      res += "  requires v.WF(c)\n" +
            "{\n" +
            "  forall idx, i, j |\n" +
            String.Format("    && 0 <= idx < |c.{0}|\n", variableField) +
            "    && v.ValidHistoryIdx(i)\n" +
            "    && v.ValidHistoryIdx(j)\n" +
            "    && i <= j\n" +
            "  ::\n" +
            string.Format("    v.History(j).{0}[idx].{1}.SatisfiesMonotonic(v.History(i).{0}[idx].{1})\n", variableField, name) +
             "}\n";
      return res;
    }

    public string ToWitnessPredicate() {
      var res = string.Format("ghost predicate {{:opaque}} {0}(c: Constants, v: Variables)\n", GetWitnessPredicateName());
      res += "  requires v.WF(c)\n" +
            "{\n" +
            "  forall idx, i |\n" +
            String.Format("    && 0 <= idx < |c.{0}|\n", variableField) +
            "    && v.ValidHistoryIdx(i)\n" +
            String.Format("    && v.History(i).{0}[idx].{1} != v.History(0).{0}[idx].{1}\n", variableField, name) +
            "  ::\n" +
            "    (exists j, step, msgOps ::\n" +
            "      && 0 <= j < i\n" +
           String.Format("      && v.History(j).{0}[idx].{1} != v.History(j+1).{0}[idx].{1}\n", variableField, name) +
           String.Format("      && v.History(j+1).{0}[idx].{1} == v.History(i).{0}[idx].{1}\n", variableField, name) +
           String.Format("      && {0}.NextStep(c.{1}[idx], v.History(j).{1}[idx], v.History(j+1).{1}[idx], step, msgOps)\n", module, variableField) +
            "    )\n" +
             "}\n";
      return res;
    }

    public string ToLemma() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetLemmaName());
      // res += "  requires v.WF(c)\n" +
      //        "  requires ValidMessages(c, v)\n" +
      //        string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
      //        "  requires Next(c, v, v')\n" +
      //        string.Format("  ensures {0}(c, v')\n", GetPredicateName()) +
      //        "{\n" +
      //        string.Format("  forall msg | msg in v'.network.sentMsgs && msg.{0}?\n", msgType) +
      //        "  ensures\n" +
      //        "  (exists i ::\n" + 
      //        "    && v'.ValidHistoryIdxStrict(i)\n" +
      //       string.Format("    && {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
      //        "  ) {\n" +
      //        "    if msg !in v.network.sentMsgs {\n" + 
      //        "      // witness and trigger\n" +
      //        "      var i := |v.history|-1;\n" +
      //        string.Format("      assert {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg);\n", module, functionName, variableField) +
      //        "    }\n" +
      //        "  }\n" +
      //        "}\n";
      return res;
    }

    public string ToWitnessLemma() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetWitnessLemmaName()) +
            "  requires v.WF(c)\n" +
            String.Format("  requires {0}(c, v)\n", GetWitnessPredicateName()) +
            "  requires Next(c, v, v')\n" +
            String.Format("  ensures {0}(c, v')\n", GetWitnessPredicateName()) +
            "{\n" +
            "  forall idx, i |\n" +
            String.Format("    && 0 <= idx < |c.{0}|\n", variableField) +
            "    && v'.ValidHistoryIdx(i)\n" +
            String.Format("    && v'.History(i).{0}[idx].{1} != v'.History(0).{0}[idx].{1}\n", variableField, name) +
            "  ensures\n" +
            "    (exists j, step, msgOps ::\n" +
            "      && 0 <= j < i\n" +
           String.Format("      && v'.History(j).{0}[idx].{1} != v'.History(j+1).{0}[idx].{1}\n", variableField, name) +
           String.Format("      && v'.History(j+1).{0}[idx].{1} == v'.History(i).{0}[idx].{1}\n", variableField, name) +
           String.Format("      && {0}.NextStep(c.{1}[idx], v'.History(j).{1}[idx], v'.History(j+1).{1}[idx], step, msgOps)\n", module, variableField) +
            "    )\n" +
            "  {\n" +  // begin forall-ensures block
            "    VariableNextProperties(c, v, v');\n" +
            "    if v'.ValidHistoryIdxStrict(i) {\n" +
            String.Format("      reveal_{0}();\n", GetWitnessPredicateName()) +
            "    } else {\n" +
            String.Format("      if v'.History(i-1).{0}[idx].{1} == v'.History(i).{0}[idx].{1} {{\n", variableField, name) +
            String.Format("        var k, step, msgOps := {0}(c, v, idx, i-1);\n", GetSkolemizationName()) +
            "        // triggers\n" +
            "        assert 0 <= k < i;\n" +
            String.Format("        assert v'.History(k).{0}[idx].{1} != v'.History(k+1).{0}[idx].{1};\n", variableField, name) +
            String.Format("        assert v'.History(k+1).{0}[idx].{1} == v'.History(i).{0}[idx].{1};\n", variableField, name) +
            String.Format("        assert {0}.NextStep(c.{1}[idx], v'.History(k).{1}[idx], v'.History(k+1).{1}[idx], step, msgOps);\n", module, variableField) +
            "      } else {\n" +
            "        // triggers and witnesses\n" +
            String.Format("        assert v'.History(i-1).{0}[idx].{1} != v'.History(i).{0}[idx].{1};\n", variableField, name) +
            "        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);\n" +
            "        var j := i-1;\n" +
            "        assert j + 1 == i;\n" +
            "        assert 0 <= j < i;\n" +
            // String.Format("        assert v'.History(j).{0}[idx].{1} != v'.History(j+1).{0}[idx].{1};\n", variableField, name) +
            String.Format("        assert v'.History(j+1).{0}[idx].{1} == v'.History(i).{0}[idx].{1};\n", variableField, name) +
            "      }\n" +
            "    }\n" +
            "  }\n" +  // end forall-ensures block
            String.Format("  assert {0}(c, v') by {{\n", GetWitnessPredicateName()) +
            String.Format("    reveal_{0}();\n", GetWitnessPredicateName()) +
            "  }\n" +
            "}\n";
      return res;
    }

    public string ToSkolemization() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, idx: int, i: nat)\n", GetSkolemizationName()) +
            String.Format("returns (j: nat, step: {0}.Step, msgOps: MessageOps)\n", module) +
            "  requires v.WF(c)\n" +
            string.Format("  requires {0}(c, v)\n", GetWitnessPredicateName()) +
            string.Format("  requires 0 <= idx < |c.{0}|\n", variableField) +
            "  requires v.ValidHistoryIdx(i)\n" +
            String.Format("  requires v.History(i).{0}[idx].{1} != v.History(0).{0}[idx].{1}\n", variableField, name) +
            "  ensures v.ValidHistoryIdxStrict(j)\n" +
            "  ensures 0 <= j < i\n" +
            String.Format("  ensures v.History(j).{0}[idx].{1} != v.History(j+1).{0}[idx].{1}\n", variableField, name) +
            String.Format("  ensures v.History(j+1).{0}[idx].{1} == v.History(i).{0}[idx].{1}\n", variableField, name) +
            String.Format("  ensures {0}.NextStep(c.{1}[idx], v.History(j).{1}[idx], v.History(j+1).{1}[idx], step, msgOps)\n", module, variableField) +
            "{\n" +
            String.Format("  reveal_{0}();\n", GetWitnessPredicateName()) +
            "  j, step, msgOps :|\n" +
            "      && 0 <= j < i\n" +
            String.Format("      && v.History(j).{0}[idx].{1} != v.History(j+1).{0}[idx].{1}\n", variableField, name) +
            String.Format("      && v.History(j+1).{0}[idx].{1} == v.History(i).{0}[idx].{1}\n", variableField, name) +
            String.Format("      && {0}.NextStep(c.{1}[idx], v.History(j).{1}[idx], v.History(j+1).{1}[idx], step, msgOps);\n", module, variableField) +
            "}\n";
      return res;
    }

    public override string ToString(){
      return string.Format("Monotonic field [{0}: {1}] in module [{2}], in DistributedSystem.[Hosts.{3}]", name, typeName, module, variableField);
    }  
  }
}
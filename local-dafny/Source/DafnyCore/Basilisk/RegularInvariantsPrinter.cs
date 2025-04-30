using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text;
using Microsoft.Boogie;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
  public static class RegularInvPrinter {

    private static readonly string[] includes = {"spec.dfy"};
    private static readonly string customInvariantsFile = "customMessageInvariants.dfy";
    private static readonly string customInvariantsModule = "CustomMessageInvariants";
    private static readonly string[] imports = {"Types", "UtilitiesLibrary", "MonotonicityLibrary", "DistributedSystem"};
    private static readonly string templatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/Basilisk/templates.json";
    
    private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(templatePath));

    public static string GetFromTemplate(string key, int indent) {
    var lines = Template[key];
    var res = new StringBuilder();
    foreach (var l in lines) {
      res.AppendLine(new string(' ', indent) + l);
    }
    return res.ToString();
  }
    public static string PrintFootprintJson(Dictionary<String, MessageUpdates> footprintMap) {
      //Ugly code to get it into nested dictionary format in order to place in JSON
      Dictionary<String, Dictionary<String, Dictionary<String, List<String>>>> footPrintDictNested 
                    = new Dictionary<String, Dictionary<String, Dictionary<String, List<String>>>>();
      foreach (KeyValuePair<String, MessageUpdates> moduleKvp in footprintMap){
        footPrintDictNested.Add(moduleKvp.Key, moduleKvp.Value.unflattenDict());
      }
      string output = JsonConvert.SerializeObject(footPrintDictNested, Newtonsoft.Json.Formatting.Indented);
      return output;
    }
    public static string PrintMonotonicityInvariants(MonotonicityInvariantsFile file, string sourceFileName) {
      var res = new StringBuilder();

      // Header
      res.AppendLine($"/// This file is auto-generated from {sourceFileName}");
      res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

      // Module preamble 
      foreach (string i in includes) {
        res.AppendLine(String.Format("include \"{0}\"", i));
      }
      res.AppendLine();
      res.AppendLine("module MonotonicityInvariants {"); // begin MonotinicityInvariants module
      foreach (string i in imports) {
        res.AppendLine(String.Format("import opened {0}", i));
      }
      res.AppendLine();

      // State invariants
      foreach (var monoInv in file.GetInvariants()) {
        res.AppendLine(monoInv.ToPredicate());
      }

      // Main monotonicity invariant
      res.AppendLine("ghost predicate MonotonicityInv(c: Constants, v: Variables)");
      res.AppendLine("{");
      res.AppendLine("  && v.WF(c)");
      foreach (var inv in file.GetInvariants()) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Proof obligations
      res.AppendLine("// Base obligation");
      res.Append(GetFromTemplate("InitImpliesMonotonicityInvHeader", 0));
      res.AppendLine("}");
      res.AppendLine();
      
      res.AppendLine("// Inductive obligation");
      res.Append(GetFromTemplate("MonotonicityInvInductiveHeader", 0));
      res.AppendLine("}");
      res.AppendLine();

      // Footer
      res.AppendLine("} // end module MonotonicityInvariants");
      return res.ToString();
    } // end function PrintMonotonicityInvariants
    

    public static string PrintMessageInvariants(MessageInvariantsFile file, string sourceFileName) {
      var res = new StringBuilder();

      // Header
      res.AppendLine($"/// This file is auto-generated from {sourceFileName}");
      res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

      // Module preamble 
      foreach (string i in includes) {
        res.AppendLine(String.Format("include \"{0}\"", i));
      }
      if (file.IncludeCustomInvariants) {
        res.AppendLine(String.Format("include \"{0}\"", customInvariantsFile));
      }
      res.AppendLine();
      res.AppendLine("module MessageInvariants {"); // begin MessageInvariants module
      foreach (string i in imports) {
        res.AppendLine(String.Format("import opened {0}", i));
      }
      if (file.IncludeCustomInvariants) {
        res.AppendLine(String.Format("import opened {0}", customInvariantsModule));
      }
      res.AppendLine();

      // Declar ValidMessges
      res.AppendLine("// All msg have a valid source");
      res.AppendLine("ghost predicate ValidMessages(c: Constants, v: Variables)");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine("  forall msg | msg in v.network.sentMsgs");
      res.AppendLine("  ::");
      res.Append("  ");
      foreach (var si in file.SendInvariants) {
        res.Append("if ");
        res.Append($"msg.{si.GetMessageType()}? ");
        res.AppendLine($"then 0 <= msg.Src() < |c.{si.GetVariableField()}|");
        res.Append("  else ");
      } 
      res.AppendLine("true");
      res.AppendLine("}");
      res.AppendLine();

      // List Send Invariants
      res.AppendLine(GetFromTemplate("ExistingMessage", 0));

      foreach (var sendInv in file.SendInvariants) {
        res.AppendLine(sendInv.ToPredicate());
      }

      // List Receive Invariants
      foreach (var recvInv in file.ReceiveInvariants) {
        res.AppendLine(recvInv.ToPredicate());
      }

      // Main message invariant
      res.AppendLine("ghost predicate MessageInv(c: Constants, v: Variables)");
      res.AppendLine("{");
      res.AppendLine("  && v.WF(c)");
      res.AppendLine("  && ValidVariables(c, v)");
      res.AppendLine("  && ValidMessages(c, v)");
      foreach (var inv in file.SendInvariants) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      foreach (var inv in file.ReceiveInvariants) {
        res.AppendLine(String.Format("  && {0}(c, v)", inv.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Proof obligations
      res.AppendLine("// Base obligation");
      res.Append(GetFromTemplate("InitImpliesMessageInvHeader", 0));
      foreach (var ri in file.ReceiveInvariants.Where(x => x.Opaque)) {
        // reveal opaqued receive invariants
        res.AppendLine(string.Format("  reveal_{0}();", ri.GetPredicateName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      res.AppendLine("// Inductive obligation");
      res.AppendLine(GetFromTemplate("MessageInvInductiveHeader", 0)); 
      res.AppendLine("{");
      res.AppendLine("  InvNextValidVariables(c, v, v');");
      foreach (var inv in file.SendInvariants) {
        res.AppendLine(String.Format("  {0}(c, v, v');", inv.GetLemmaName()));
      }
      foreach (var inv in file.ReceiveInvariants) {
        res.AppendLine(String.Format("  {0}(c, v, v');", inv.GetLemmaName()));
      }
      res.AppendLine("}");
      res.AppendLine();

      // Begin proofs section
      res.AppendLine(GetFromTemplate("AuxProofsSeparator", 0));

      // InvNextProofs
      foreach (var si in file.SendInvariants) {
        res.AppendLine(si.ToLemma());
      }
      foreach (var ri in file.ReceiveInvariants) {
        res.AppendLine(ri.ToLemma());
      }

      // Begin skolemization section
      res.AppendLine(GetFromTemplate("SkolemizationsSeparator", 0));

      foreach (var si in file.SendInvariants) {
        res.AppendLine(si.ToSkolemization());
      }
      foreach (var skolem in file.ReceiveSkolemizations) {
        res.AppendLine(skolem.ToSkolemization());
      }

      // Footer
      res.AppendLine("} // end module MessageInvariants");
      return res.ToString();
    } // end function PrintMessageInvariants

    // Warning: Only supports up to two host types here
    public static string PrintOwnershipInvariants(OwnershipInvariantsFile file, string sourceFileName) {
      var invariants = new List<string>(); // keep track of a list of invariants 
      
      var res = new StringBuilder();
      res.AppendLine($"/// This file is auto-generated from {sourceFileName}");
      res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

      // Module preamble 
      foreach (string i in includes) {
        res.AppendLine(String.Format("include \"{0}\"", i));
      }
      res.AppendLine();
      res.AppendLine("module OwnershipInvariants {"); // begin OwnershipInvariants module
      foreach (string i in imports) {
        res.AppendLine(String.Format("import opened {0}", i));
      }
      res.AppendLine();
      res.AppendLine(GetFromTemplate("DefinitionsSeparator", 0));

      // print predicate UniqueKeyInFlight
      res.AppendLine(GetFromTemplate("UniqueKeyInFlight", 0));

      // print predicate KeyInFlightByMessage
      res.AppendLine("// Disjunction for each host type");
      res.AppendLine("ghost predicate {:trigger UniqueKeyInFlight} KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey)");
      res.AppendLine("   requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine("  && msg in v.network.sentMsgs");
      res.Append("  && (");  // open disjunct
      foreach (var kvp in file.ExtractHosts()) {
        var field = kvp.Value; var mod = kvp.Key;
        res.AppendLine($"      || (0 <= msg.Dst() < |c.{field}| &&");
        res.AppendLine($"         {mod}.UniqueKeyInFlightForHost(c.{field}[msg.Dst()], v.Last().{field}[msg.Dst()], k, msg)");
        res.AppendLine("       )");
      }
      res.AppendLine("     )");  // close disjunct
      res.AppendLine("}");
      res.AppendLine();

      // print NoHostOwnKey for each host type
      foreach (var kvp in file.ExtractHosts()) {
        var field = kvp.Value; var mod = kvp.Key;
        res.AppendLine("// One for each host type");
        PrintNoHostOwnsKeyGroup(res, mod, field);
        res.AppendLine();
      }

      // print NoHostOwnKeyMain
      res.AppendLine("// Conjunction of corresponding assertions for each host type");
      res.AppendLine("ghost predicate {:trigger KeyInFlightByMessage, UniqueKeyInFlight} NoHostOwnsKeyMain(c: Constants, v: Variables, k: UniqueKey)");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      foreach (var kvp in file.ExtractHosts()) {
        var mod = kvp.Key;
        res.AppendLine($"  && No{mod}OwnsKey(c, v, k)");
      }
      res.AppendLine("}");
      res.AppendLine();
      res.AppendLine(GetFromTemplate("InvariantsSeparator", 0));
      res.AppendLine();

      // print AtMostOneInFlightMessagePerKey
      res.AppendLine(GetFromTemplate("AtMostOneInFlightMessagePerKey", 0));
      invariants.Add("AtMostOneInFlightMessagePerKey");
      res.AppendLine();

      // print HostOwnsKeyImpliesNotInFlight
      PrintHostOwnsKeyImpliesNotInFlight(file, res);
      invariants.Add($"HostOwnsKeyImpliesNotInFlight");

      // print AtMostOneOwnerPerKey for each host type
      foreach (var kvp in file.ExtractHosts()) {
        var field = kvp.Value; var mod = kvp.Key;
        res.AppendLine("// One for each host type");
        PrintAtMostOneOwnerPerKey(res, mod, field, invariants);
        res.AppendLine();
      }

      // print HostOwnKey if more than one host type
      if (file.ExtractHosts().Count > 1) {
        var hostTypes = new List<string>(file.ExtractHosts().Keys);
        foreach (var h in hostTypes) {
          foreach (var other in hostTypes) {
            if (other != h) {
              res.AppendLine("// One for each host type");
            PrintHostOwnKey(res, h, other, invariants);
            res.AppendLine();
            }
          }
        }
      }

      // print proof obligations
      PrintOwnershipInvariantsObligations(res, invariants);

      res.AppendLine(GetFromTemplate("AuxProofsSeparator", 0));

      // print proofs
      // print InvNextAtMostOneInFlightMessagePerKey
      res.AppendLine(GetFromTemplate("InvNextAtMostOneInFlightMessagePerKey", 0));
      res.AppendLine(GetFromTemplate("InvNextAtMostOneInFlightHelper", 0));

      // print InvNextHostOwnsKeyImpliesNotInFlight
      res.AppendLine(GetFromTemplate("InvNextHostOwnsKeyImpliesNotInFlight", 0));

      // print InvNextAtMostOneOwnerPerKey for each host type
      foreach (var kvp in file.ExtractHosts()) {
        var field = kvp.Value; var mod = kvp.Key;
        res.AppendLine("// One for each host type");
        PrintInvNextAtMostOneOwnerPerKey(res, mod, field);
        res.AppendLine();
      }

      // print InvNextHostOwnKey if more than one host type
      if (file.ExtractHosts().Count > 1) {
        var hostTypes = new List<string>(file.ExtractHosts().Keys);
        foreach (var h in hostTypes) {
          foreach (var other in hostTypes) {
            if (other != h) {
              res.AppendLine("// One for each host type");
            PrintInvNextHostOwnKey(res, h, file.ExtractHosts()[h], other);
            res.AppendLine();
            }
          }
        }
      }



      res.AppendLine("}  // end OwnershipInvariants module");
      return res.ToString();
    }

    private static void PrintOwnershipInvariantsObligations(StringBuilder res, List<string> invariants) {
      // print OwnershipInv
      res.AppendLine("ghost predicate OwnershipInv(c: Constants, v: Variables)");
      res.AppendLine("{");
      res.AppendLine("  && v.WF(c)");
      foreach (var inv in invariants) {
        res.AppendLine($"  && {inv}(c, v)");
      }
      res.AppendLine("}");
      res.AppendLine();
      
      // InitImpliesOwnershipInv
      res.AppendLine(GetFromTemplate("InitImpliesOwnershipInv", 0));

      // OwnershipInvInductive
      res.Append(GetFromTemplate("OwnershipInvInductiveHeader", 0));
      foreach (var inv in invariants) {
        res.AppendLine($"  InvNext{inv}(c, v, v');");
      }
      res.AppendLine("}");
      res.AppendLine();
    }

    // Print the NoHostOwnsKey group for given host type
    private static void PrintNoHostOwnsKeyGroup(StringBuilder res, string mod, string field) {
      res.AppendLine($"ghost predicate No{mod}OwnsKey(c: Constants, v: Variables, k: UniqueKey)");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine($"  forall idx | 0 <= idx < |c.{field}|");
      res.AppendLine("  ::");
      res.AppendLine($"  !{mod}.HostOwnsUniqueKey(c.{field}[idx], v.Last().{field}[idx], k)");
      res.AppendLine("}");
    }

    // Print HostOwnsKeyImpliesNotInFlight
    private static void PrintHostOwnsKeyImpliesNotInFlight(OwnershipInvariantsFile file, StringBuilder res) {
      var triggers =  new List<string>();
      foreach (var kvp in file.ExtractHosts()) {
        var mod = kvp.Key;
        triggers.Add($"{mod}.HostOwnsUniqueKey");
      }
      res.AppendLine($"ghost predicate {{:trigger {string.Join(",", triggers)}}}");
      res.AppendLine(GetFromTemplate("HostOwnsKeyImpliesNotInFlightSuffix", 0));
    }

    // Print the AtMostOneOwnerPerKey group for given host type
    private static void PrintAtMostOneOwnerPerKey(StringBuilder res, string mod, string field, List<string> invariants) {
      res.AppendLine($"ghost predicate AtMostOneOwnerPerKey{mod}(c: Constants, v: Variables)");
      invariants.Add($"AtMostOneOwnerPerKey{mod}");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine($"  forall h1, h2, k |");
      res.AppendLine($"    && 0 <= h1 < |c.{field}| && 0 <= h2 < |c.{field}|");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[h1], v.Last().{field}[h1], k)");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[h2], v.Last().{field}[h2], k)");
      res.AppendLine("  ::");
      res.AppendLine("    h1 == h2");
      res.AppendLine("}");
    }

    // Print the InvNextAtMostOneOwnerPerKey group for given host type
    private static void PrintInvNextAtMostOneOwnerPerKey(StringBuilder res, string mod, string field) {
      res.AppendLine($"lemma InvNextAtMostOneOwnerPerKey{mod}(c: Constants, v: Variables, v': Variables)");
      res.AppendLine("  requires v'.WF(c)");
      res.AppendLine("  requires OwnershipInv(c, v)");
      res.AppendLine("  requires Next(c, v, v')");
      res.AppendLine($"  ensures AtMostOneOwnerPerKey{mod}(c, v')");
      res.AppendLine("{");
      res.AppendLine($"  forall h1, h2, k |");
      res.AppendLine($"    && 0 <= h1 < |c.{field}| && 0 <= h2 < |c.{field}|");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[h1], v'.Last().{field}[h1], k)");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[h2], v'.Last().{field}[h2], k)");
      res.AppendLine("  ensures");
      res.AppendLine("    h1 == h2");
      res.AppendLine("  {");
      res.AppendLine("    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);");
      res.AppendLine("    if h1 != h2 {");
      res.AppendLine("      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k); ");
      res.AppendLine("      assert UniqueKeyInFlight(c, v, k);");
      res.AppendLine("    }");
      res.AppendLine("  }");
      res.AppendLine("}");
    }

    // Print the HostOwnKey group for given host type
    private static void PrintHostOwnKey(StringBuilder res, string mod, string otherMod, List<string> invariants) {
      res.AppendLine($"ghost predicate {mod}OwnKey(c: Constants, v: Variables)");
      invariants.Add($"{mod}OwnKey");
      res.AppendLine("  requires v.WF(c)");
      res.AppendLine("{");
      res.AppendLine($"  forall k | !No{mod}OwnsKey(c, v, k) :: No{otherMod}OwnsKey(c, v, k)");
      res.AppendLine("}");
    }

    // Print the HostOwnKey group for given host type
    private static void PrintInvNextHostOwnKey(StringBuilder res, string mod, string field, string otherMod) {
      res.AppendLine($"lemma InvNext{mod}OwnKey(c: Constants, v: Variables, v': Variables) ");
      res.AppendLine("  requires v'.WF(c)");
      res.AppendLine("  requires OwnershipInv(c, v)");
      res.AppendLine("  requires Next(c, v, v')");
      res.AppendLine($"  ensures {mod}OwnKey(c, v')");
      res.AppendLine("{");
      res.AppendLine($"  forall k | !No{mod}OwnsKey(c, v', k)");
      res.AppendLine($"  ensures No{otherMod}OwnsKey(c, v', k) {{");
      
      res.AppendLine("    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);");
      res.AppendLine($"    var idx :| 0 <= idx < |c.{field}| && {mod}.HostOwnsUniqueKey(c.{field}[idx], v'.Last().{field}[idx], k);");
      res.AppendLine($"    if {mod}.HostOwnsUniqueKey(c.{field}[idx], v.Last().{field}[idx], k) {{");
      res.AppendLine("      assert !UniqueKeyInFlight(c, v, k);");
      res.AppendLine($"      if !No{otherMod}OwnsKey(c, v', k) {{");
      res.AppendLine("        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);");
      res.AppendLine("        assert false;");
      res.AppendLine("      }");
      res.AppendLine("    } else {");
      res.AppendLine("      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);");
      res.AppendLine("      assert UniqueKeyInFlight(c, v, k);");
      res.AppendLine("    }");
      res.AppendLine("  }");
      res.AppendLine("}");
    }    
  } // end class MessageInvariantsFile
}
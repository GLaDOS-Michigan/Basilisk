using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
public static class DistributedSystemPrinter {

  private static readonly string[] Includes = {"../hosts.dfy"};
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "Network"};
  private static readonly string TemplatePath = "/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Source/DafnyCore/Kondo/templates.json";

  private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(TemplatePath));

  private static string GetFromTemplate(string key, int indent) {
    var lines = Template[key];
    var res = new StringBuilder();
    foreach (var l in lines) {
      res.AppendLine(new string(' ', indent) + l);
    }
    return res.ToString();
  }

  public static string PrintDistributedSystem(DistributedSystemFile file, DafnyOptions options, string sourceFileName) {
    var res = new StringBuilder();

    // Header
    res.AppendLine($"/// This file is auto-generated from {sourceFileName}");
    res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

    // Dafny files to include
    foreach (string i in Includes) {
      res.AppendLine(String.Format("include \"{0}\"", i));
    }
    res.AppendLine();

    // Define Network module
    res.AppendLine(GetFromTemplate("NetworkModule", 0));
    
    // Define DistributedSystem module
    res.AppendLine("module DistributedSystem {");
    res.AppendLine(PrintDistributedSystemModuleBody(file, options));
    res.AppendLine("} // end module DistributedSystem");
    return res.ToString();
  } // end function PrintDistributedSystem

  private static string PrintDistributedSystemModuleBody(DistributedSystemFile file, DafnyOptions options) {
    var res = new StringBuilder();

    // Import dependencies
    foreach (string i in Imports) {
      res.AppendLine(String.Format("  import opened {0}", i));
    }
    foreach (string i in file.GetHostImports()) {
      res.AppendLine(String.Format("  import {0}", i));
    }
    res.AppendLine();
    
    // Declare datatype Constants
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintDatatype(file.GetConstants(), 2, "dummy string");
    res.Append(StripTriggerAnnotations(wr.ToString()));
    res.AppendLine("  // end datatype Constants");
    res.AppendLine();

    // Declare datatype Hosts
    // Hosts is the same as Variables in sync version, with a renaming of the datatype and 
    // datatype constructor
    wr = new StringWriter();
    printer = new Printer(wr, options);
    printer.PrintDatatype(file.GetVariables(), 2, "dummy string");
    var variablesDecl = wr.ToString();
    var hostsDecl = variablesDecl.Replace(
        "datatype Variables = Variables", 
        "datatype Hosts = Hosts"
    );  // hacky renaming strategy
    res.Append(hostsDecl);
    res.AppendLine("  // end datatype Hosts");
    res.AppendLine();

    // Declare datatype Variables
    res.AppendLine(GetFromTemplate("DatatypeVariables", 2));
    res.AppendLine();

    // Declare Init relations
    res.Append(GetFromTemplate("InitHostsHeader", 2));
    var initConjuncts = Expression.Conjuncts(file.GetInitRelation().Body).ToList();
    foreach (var expr in initConjuncts) {
      var exprStr = expr.ToString();
      if (exprStr.Contains("GroupInit")) {
        exprStr = exprStr.Replace("v.", "h.");  // hacky, but works for now
        res.AppendLine("    && " + exprStr);
      }
    }
    res.AppendLine("  }");
    res.AppendLine();
    res.AppendLine(GetFromTemplate("Init", 2));

    // Declare datatype Step
    res.AppendLine("  datatype Step = ");
    foreach (var kvp in file.ExtractHosts()) {
      var line = string.Format("    | {0}Step(actor: nat, msgOps: MessageOps)", kvp.Key);
      res.AppendLine(line);
    }
    res.AppendLine();

    // Declare NextStep relation
    res.Append(GetFromTemplate("NextStepHeader", 2));
    foreach (var kvp in file.ExtractHosts()) {
      var line = string.Format("      case {0}Step(actor, msgOps) => Next{0}Step(c, h, h', actor, msgOps)", kvp.Key);
      res.AppendLine(line);
    }
    res.AppendLine("  }");
    res.AppendLine();

    // Declare NextHostStep relations
    foreach (var kvp in file.ExtractHosts()) {
      res.AppendLine(string.Format("  ghost predicate Next{0}Step(c: Constants, h: Hosts, h': Hosts, actor: nat, msgOps: MessageOps)", kvp.Key));
      res.AppendLine("    requires h.WF(c) && h'.WF(c)");
      res.AppendLine("  {");
      res.AppendLine("    && " + ValidActorIdx("actor", kvp.Value));
      res.AppendLine(string.Format("    && {0}.Next(c.{1}[actor], h.{1}[actor], h'.{1}[actor], msgOps)", kvp.Key, kvp.Value));
      res.AppendLine("    // all other hosts UNCHANGED");
      foreach (var kvp2 in file.ExtractHosts()) {
        if (kvp2.Key == kvp.Key) {
          res.AppendLine(string.Format("    && (forall other| {0} && other != actor :: h'.{1}[other] == h.{1}[other])", ValidActorIdx("other", kvp.Value), kvp.Value));
        } else {
          res.AppendLine(string.Format("    && h'.{0} == h.{0}", kvp2.Value));
        }
      }
      res.AppendLine("  }");
      res.AppendLine();
    }

    // Declare Next relation
    res.AppendLine(GetFromTemplate("Next", 2));

    res.AppendLine(GetFromTemplate("VariablePropertiesSeperator", 0));

    // Declare all variable properties
    res.AppendLine(GetFromTemplate("ValidHistory", 2));
    res.AppendLine(GetFromTemplate("ValidVariables", 2));
    res.AppendLine(GetFromTemplate("InitImpliesValidVariables", 2));
    res.AppendLine(GetFromTemplate("InvNextValidVariables", 2));
    res.Append(GetFromTemplate("VariableNextProperties", 2));

    // Done
    return res.ToString();
  } // end function PrintDistributedSystemModuleBody


  private static string StripTriggerAnnotations(string input) {
    // Define the pattern to remove
    string pattern = @"\{:trigger [^\}]*\} ";
    // Use Regex.Replace to remove all occurrences of the pattern
    string resultString = Regex.Replace(input, pattern, "");
    return resultString;
  }

  private static string ValidActorIdx(string actor, string field) {
    return string.Format("0 <= {0} < |h.{1}|", actor, field);
  }
} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny
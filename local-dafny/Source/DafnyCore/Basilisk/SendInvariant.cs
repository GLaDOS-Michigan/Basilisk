using System;
using System.Diagnostics;

namespace Microsoft.Dafny
{

  public class SendInvariant {

    private string functionName;  // name of the send predicate
    private string msgType;   // name of the type of message concerning this predicate
    private string module;   // name of the module this function belongs
    private string variableField;   // which field in distributedSystem.Hosts?
    private bool isRecvAndSend;  // is this a Basilisk Receive-And-Send action

    public SendInvariant(string functionName, string msgType, string module, string variableField, bool isRecvAndSend) {
      this.functionName = functionName;
      this.msgType = msgType;
      this.module = module;
      this.variableField = variableField;
      this.isRecvAndSend = isRecvAndSend;
    }

    public static SendInvariant FromFunction(Function sendPredicate, DatatypeDecl dsHosts) {
      // Determine if this step is a Basilisk Receive-And-Send step
      bool isRecvAndSend = false;
      if (sendPredicate.Name.Contains("Receive")) {
        isRecvAndSend = true;
      }

      // Extract module and msgType
      var module = ExtractSendInvariantModule(sendPredicate);
      var msgType = ExtractSendInvariantMsgType(sendPredicate, isRecvAndSend);
      
      // Extract field name in DistributedSystem.Hosts of type seq<[module].Variables>
      string variableField = null;
      foreach (var formal in dsHosts.GetGroundingCtor().Formals) {
        if (formal.DafnyName.Contains(string.Format("{0}.Variables", module))) {
          variableField = formal.CompileName;
          break;
        }
      }
      Debug.Assert(variableField != null, "variableField should not be null");

      var sendInv = new SendInvariant(sendPredicate.Name, msgType, module, variableField, isRecvAndSend);
      Console.WriteLine(sendInv);
      Console.WriteLine();
      return sendInv;
    }

    private static string ExtractSendInvariantMsgType(Function func, bool isRecvAndSend) {
      if (isRecvAndSend) {
        var keyword = "Send";
        // Function name is of format "Receive<MsgTypeA>Send<MsgTypeB>"
        int index = func.Name.IndexOf(keyword);
        Debug.Assert(index != -1, "error extracting message type of Send Invariant");
        return func.Name.Substring(index + keyword.Length);  // +keyword.Length to get the part after the keyword
      }
      // Function name is of format "Send<MsgType>"
      return func.Name.Substring(4);
    }

    // Get the Module in Module.SendPredicate
    private static string ExtractSendInvariantModule(Function func) {
      return func.FullDafnyName.Substring(0, func.FullDafnyName.IndexOf('.'));
    }
    
    public string GetName() {
      return this.functionName;
    }

    public string GetMessageType() {
      return msgType;
    }

    public string GetVariableField() {
      return variableField;
    }

    public string GetHostModule() {
      return module;
    }

    public string GetPredicateName() {
      return string.Format("Send{0}Validity", this.msgType);
    }

    public string GetLemmaName() {
      return string.Format("InvNextSend{0}Validity", this.msgType);
    }

    public string GetSkolemizationName() {
      return string.Format("Send{0}Skolemization", this.msgType);
    }

    public string ToPredicate() {
      if (isRecvAndSend) {
        return toPredicateRecvSend();
      } else {
        return toPredicateCommon();
      }
    }

    private string toPredicateRecvSend() {
      var res = "";
      // Top-level predicate
      res += string.Format("ghost predicate {0}(c: Constants, v: Variables)\n", GetPredicateName()) +
            "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            "{\n" +
          string.Format("  forall msg | msg in v.network.sentMsgs && msg.{0}?\n", msgType) +
            "  ::\n" +
          string.Format("  {0}Body(c, v, msg)\n", GetPredicateName()) +
          "}\n" +
          "\n";

      // Helper predicate body
      res += string.Format("ghost predicate {0}Body(c: Constants, v: Variables, msg: Message)\n", GetPredicateName()) +
            "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            "  requires msg in v.network.sentMsgs\n" +
            string.Format("  requires msg.{0}?\n", msgType) +
            "{\n" +
            "  exists i, inMsg ::\n" + 
            "    && v.ValidHistoryIdxStrict(i)\n" +
            "    && ExistingMessage(v, inMsg)\n" +
          string.Format("    && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], inMsg, msg)\n", module, functionName, variableField) +
            "}\n";
      return res;
    }

    private string toPredicateCommon() {
      var res = string.Format("ghost predicate {0}(c: Constants, v: Variables)\n", GetPredicateName()) +
            "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            "{\n" +
          string.Format("  forall msg | msg in v.network.sentMsgs && msg.{0}?\n", msgType) +
            "  ::\n" +
            "  (exists i ::\n" + 
              "    && v.ValidHistoryIdxStrict(i)\n" +
          string.Format("    && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
          "  )\n" +
             "}\n";
      return res;
    }

    public string ToLemma() {
      if (isRecvAndSend) {
        return toLemmaRecvSend();
      } else {
        return toLemmaCommon();
      }
    }

    private string toLemmaRecvSend() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetLemmaName());
      var assertExistingMessageBy = 
            "      assert ExistingMessage(v', inMsg) by {\n" +
            "        reveal_ExistingMessage();\n" +
            "      }\n";

      res += "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
            "  requires Next(c, v, v')\n" +
            string.Format("  ensures {0}(c, v')\n", GetPredicateName()) +
            "{\n" +
            string.Format("  forall msg | msg in v'.network.sentMsgs && msg.{0}?\n", msgType) +
            string.Format("  ensures {0}Body(c, v', msg)\n", GetPredicateName()) +
            "  {\n" +
            "    VariableNextProperties(c, v, v');\n" + 
            "    if msg !in v.network.sentMsgs {\n" + 
            "      // witness and trigger\n" +
            "      var i := |v.history|-1;\n" +
            "      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);\n" +
            "      var inMsg := dsStep.msgOps.recv.value;\n" +
            string.Format("      assert {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], inMsg, msg);\n", module, functionName, variableField) +
            assertExistingMessageBy +
            "    } else {\n" +
            "      // witness and trigger\n" +
            string.Format("      var i, inMsg :| v.ValidHistoryIdxStrict(i) && ExistingMessage(v, inMsg) && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], inMsg, msg);\n", module, functionName, variableField) +
            assertExistingMessageBy +
            "    }\n" +
            "  }\n" +
            "}\n";
      return res;
    }

    private string toLemmaCommon() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetLemmaName()) +
      "  requires v.WF(c)\n" +
      "  requires ValidMessages(c, v)\n" +
      string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
      "  requires Next(c, v, v')\n" +
      string.Format("  ensures {0}(c, v')\n", GetPredicateName()) +
      "{\n" +
      string.Format("  forall msg | msg in v'.network.sentMsgs && msg.{0}?\n", msgType) +
      "  ensures\n" +
      "  (exists i ::\n" + 
      "    && v'.ValidHistoryIdxStrict(i)\n" +
      string.Format("    && {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
      "  ) {\n" +
      "    VariableNextProperties(c, v, v');\n" + 
      "    if msg !in v.network.sentMsgs {\n" + 
      "      // witness and trigger\n" +
      "      var i := |v.history|-1;\n" +
      string.Format("      assert {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg);\n", module, functionName, variableField) +
      "    }\n" +
      "  }\n" +
      "}\n";
      return res;
    }

    public override string ToString(){
      return string.Format("Send predicate [{0}] in module [{1}] for msg type [{2}], in DistributedSystem.[Hosts.{3}]. IsRecvAndSend: [{4}]", functionName, module, msgType, variableField, isRecvAndSend);
    }  

    public string ToSkolemization() {
      if (isRecvAndSend) {
        return toSkolemizationRecvSend();
      } else {
        return toSkolemizationCommon();
      }
    }

    private string toSkolemizationRecvSend() {
      var assertExistingMessageBy = 
            "  assert inMsg in v.network.sentMsgs by {\n" +
            "    reveal_ExistingMessage();\n" +
            "  }\n";

      var res = string.Format("lemma {0}(c: Constants, v: Variables, msg: Message)\n", GetSkolemizationName()) +
            "returns (i: nat, inMsg: Message)\n" +
            "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
            "  requires msg in v.network.sentMsgs\n" +
            string.Format("  requires msg.{0}?\n", msgType) +
            "  ensures v.ValidHistoryIdxStrict(i)\n" +
            "  ensures inMsg in v.network.sentMsgs\n" +
            string.Format("  ensures {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], inMsg, msg)\n", module, functionName, variableField) +
            "{\n" +
            "  i, inMsg :|\n" +
            "      && v.ValidHistoryIdxStrict(i)\n" +
            "      && ExistingMessage(v, inMsg)\n" +
            string.Format("      && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], inMsg, msg);\n", module, functionName, variableField) +
            assertExistingMessageBy +
            "}\n";
      return res;
    }

    private string toSkolemizationCommon() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, msg: Message)\n", GetSkolemizationName()) +
            "returns (i: nat)\n" +
            "  requires v.WF(c)\n" +
            "  requires ValidMessages(c, v)\n" +
            string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
            "  requires msg in v.network.sentMsgs\n" +
            string.Format("  requires msg.{0}?\n", msgType) +
            "  ensures v.ValidHistoryIdxStrict(i)\n" +
            string.Format("  ensures {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
            "{\n" +
            "  i :|\n" +
            "      && v.ValidHistoryIdxStrict(i)\n" +
            string.Format("      && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], msg);\n", module, functionName, variableField) +
            "}\n";
      return res;
    }
  }
}
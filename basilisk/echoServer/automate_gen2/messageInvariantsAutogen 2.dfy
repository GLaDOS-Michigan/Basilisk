/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/basilisk/echoServer/automate_gen2/distributedSystem.dfy
/// Generated 03/07/2025 21:42 Pacific Standard Time
include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

// All msg have a valid source
ghost predicate ValidMessages(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs
  ::
  if msg.Response? then 0 <= msg.Src() < |c.servers|
  else if msg.Request? then 0 <= msg.Src() < |c.clients|
  else true
}

ghost predicate {:opaque} ExistingMessage(v: Variables, msg: Message) {
  msg in v.network.sentMsgs
}

ghost predicate SendResponseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Response?
  ::
  SendResponseValidityBody(c, v, msg)
}

ghost predicate SendResponseValidityBody(c: Constants, v: Variables, msg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Response?
{
  exists i, inMsg ::
    && v.ValidHistoryIdxStrict(i)
    && ExistingMessage(v, inMsg)
    && ServerHost.ReceiveRequestSendResponse(c.servers[msg.Src()], v.History(i).servers[msg.Src()], v.History(i+1).servers[msg.Src()], inMsg, msg)
}

ghost predicate SendRequestValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Request?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && ClientHost.SendRequest(c.clients[msg.Src()], v.History(i).clients[msg.Src()], v.History(i+1).clients[msg.Src()], msg)
  )
}

ghost predicate {:opaque} ClientHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.clients|
    && v.History(i).clients[idx] !=  v.History(0).clients[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).clients[idx] != v.History(j+1).clients[idx])
       && (v.History(j+1).clients[idx] == v.History(i).clients[idx])
       && ClientHost.NextStep(c.clients[idx], v.History(j).clients[idx], v.History(j+1).clients[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} ClientHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.clients|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).clients[idx] != v.History(j+1).clients[idx])
       && (v.History(j+1).clients[idx] == v.History(i).clients[idx])
       && ClientHost.NextStep(c.clients[idx], v.History(j).clients[idx], v.History(j+1).clients[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate {:opaque} ServerHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.servers|
    && v.History(i).servers[idx] !=  v.History(0).servers[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).servers[idx] != v.History(j+1).servers[idx])
       && (v.History(j+1).servers[idx] == v.History(i).servers[idx])
       && ServerHost.NextStep(c.servers[idx], v.History(j).servers[idx], v.History(j+1).servers[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} ServerHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.servers|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).servers[idx] != v.History(j+1).servers[idx])
       && (v.History(j+1).servers[idx] == v.History(i).servers[idx])
       && ServerHost.NextStep(c.servers[idx], v.History(j).servers[idx], v.History(j+1).servers[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && ValidMessages(c, v)
  && SendResponseValidity(c, v)
  && SendRequestValidity(c, v)
  && ClientHostReceiveValidity(c, v)
  && ServerHostReceiveValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_ClientHostReceiveValidity();
  reveal_ServerHostReceiveValidity();
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')

{
  InvNextValidVariables(c, v, v');
  InvNextSendResponseValidity(c, v, v');
  InvNextSendRequestValidity(c, v, v');
  InvNextClientHostReceiveValidity(c, v, v');
  InvNextServerHostReceiveValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextSendResponseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendResponseValidity(c, v)
  requires Next(c, v, v')
  ensures SendResponseValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Response?
  ensures SendResponseValidityBody(c, v', msg)
  {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var inMsg := dsStep.msgOps.recv.value;
      assert ServerHost.ReceiveRequestSendResponse(c.servers[msg.Src()], v'.History(i).servers[msg.Src()], v'.History(i+1).servers[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    } else {
      // witness and trigger
      var i, inMsg :| v.ValidHistoryIdxStrict(i) && ExistingMessage(v, inMsg) && ServerHost.ReceiveRequestSendResponse(c.servers[msg.Src()], v.History(i).servers[msg.Src()], v.History(i+1).servers[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    }
  }
}

lemma InvNextSendRequestValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendRequestValidity(c, v)
  requires Next(c, v, v')
  ensures SendRequestValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Request?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && ClientHost.SendRequest(c.clients[msg.Src()], v'.History(i).clients[msg.Src()], v'.History(i+1).clients[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert ClientHost.SendRequest(c.clients[msg.Src()], v'.History(i).clients[msg.Src()], v'.History(i+1).clients[msg.Src()], msg);
    }
  }
}

lemma ClientHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: ClientHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ClientHostReceiveValidity(c, v)
  requires 0 <= idx < |c.clients|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).clients[idx] != v.History(0).clients[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).clients[idx] != v.History(j+1).clients[idx]
  ensures v.History(j+1).clients[idx] == v.History(i).clients[idx]
  ensures ClientHost.NextStep(c.clients[idx], v.History(j).clients[idx], v.History(j+1).clients[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_ClientHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).clients[idx] != v.History(j+1).clients[idx])
      && (v.History(j+1).clients[idx] == v.History(i).clients[idx])
      && ClientHost.NextStep(c.clients[idx], v.History(j).clients[idx], v.History(j+1).clients[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextClientHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ClientHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures ClientHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.clients|
    && v'.History(i).clients[idx] != v'.History(0).clients[idx]
  ensures
    ClientHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert ClientHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ClientHostReceiveValidity();
       reveal_ClientHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).clients[idx] == v'.History(i).clients[idx] {
        var k, step, msgOps := ClientHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).clients[idx] != v'.History(k+1).clients[idx];
        assert v'.History(k+1).clients[idx] == v'.History(i).clients[idx];
        assert ClientHost.NextStep(c.clients[idx], v'.History(k).clients[idx], v'.History(k+1).clients[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).clients[idx] != v'.History(i).clients[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).clients[idx] == v'.History(i).clients[idx];
      }
      assert ClientHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ClientHostReceiveValidity();
       reveal_ClientHostReceiveValidityPost();
      }
    }
  }
  assert ClientHostReceiveValidity(c, v') by {
    reveal_ClientHostReceiveValidity();
    reveal_ClientHostReceiveValidityPost();
  }
}

lemma ServerHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: ServerHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ServerHostReceiveValidity(c, v)
  requires 0 <= idx < |c.servers|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).servers[idx] != v.History(0).servers[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).servers[idx] != v.History(j+1).servers[idx]
  ensures v.History(j+1).servers[idx] == v.History(i).servers[idx]
  ensures ServerHost.NextStep(c.servers[idx], v.History(j).servers[idx], v.History(j+1).servers[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_ServerHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).servers[idx] != v.History(j+1).servers[idx])
      && (v.History(j+1).servers[idx] == v.History(i).servers[idx])
      && ServerHost.NextStep(c.servers[idx], v.History(j).servers[idx], v.History(j+1).servers[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextServerHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ServerHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures ServerHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.servers|
    && v'.History(i).servers[idx] != v'.History(0).servers[idx]
  ensures
    ServerHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert ServerHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ServerHostReceiveValidity();
       reveal_ServerHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).servers[idx] == v'.History(i).servers[idx] {
        var k, step, msgOps := ServerHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).servers[idx] != v'.History(k+1).servers[idx];
        assert v'.History(k+1).servers[idx] == v'.History(i).servers[idx];
        assert ServerHost.NextStep(c.servers[idx], v'.History(k).servers[idx], v'.History(k+1).servers[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).servers[idx] != v'.History(i).servers[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).servers[idx] == v'.History(i).servers[idx];
      }
      assert ServerHostReceiveValidityPost(c, v', i, idx) by {
       reveal_ServerHostReceiveValidity();
       reveal_ServerHostReceiveValidityPost();
      }
    }
  }
  assert ServerHostReceiveValidity(c, v') by {
    reveal_ServerHostReceiveValidity();
    reveal_ServerHostReceiveValidityPost();
  }
}

/***************************************************************************************
*                                  Skolemizations                                      *
***************************************************************************************/

lemma SendResponseSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendResponseValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Response?
  ensures v.ValidHistoryIdxStrict(i)
  ensures inMsg in v.network.sentMsgs
  ensures ServerHost.ReceiveRequestSendResponse(c.servers[msg.Src()], v.History(i).servers[msg.Src()], v.History(i+1).servers[msg.Src()], inMsg, msg)
{
  i, inMsg :|
      && v.ValidHistoryIdxStrict(i)
      && ExistingMessage(v, inMsg)
      && ServerHost.ReceiveRequestSendResponse(c.servers[msg.Src()], v.History(i).servers[msg.Src()], v.History(i+1).servers[msg.Src()], inMsg, msg);
  assert inMsg in v.network.sentMsgs by {
    reveal_ExistingMessage();
  }
}

lemma SendRequestSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendRequestValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Request?
  ensures v.ValidHistoryIdxStrict(i)
  ensures ClientHost.SendRequest(c.clients[msg.Src()], v.History(i).clients[msg.Src()], v.History(i+1).clients[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && ClientHost.SendRequest(c.clients[msg.Src()], v.History(i).clients[msg.Src()], v.History(i+1).clients[msg.Src()], msg);
}

ghost predicate ReceiveResponseWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.clients|
{
  && a1 in v.History(i).clients[idx].responses
  && (v.History(i).clients[idx].responses != v.History(0).clients[idx].responses)
}

lemma ReceiveResponseStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires ClientHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.clients|
  requires ReceiveResponseWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveResponseWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveResponseWitnessCondition(c, v, j+1, idx, a1)
  ensures ClientHost.ReceiveResponse(c.clients[idx], v.History(j).clients[idx], v.History(j+1).clients[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := ClientHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveResponseWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceiveResponseStepSkolemization(c, v, xj, idx, a1);
  }
}

} // end module MessageInvariants

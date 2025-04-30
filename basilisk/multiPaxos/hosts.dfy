include "types.dfy"
include "../lib/MonotonicityLibrary.dfy"

module Host {
import opened MonotonicityLibrary
import opened UtilitiesLibrary
import opened Types

datatype Constants = Constants(id: HostId, f: nat, preferredValue: Value, logCap: int)
{
  predicate ValidSlot(slot: int) {
    0 <= slot < logCap
  }

  predicate WF() {
    0 < logCap
  }
}

ghost predicate ConstantsValid(c: Constants, id: HostId, f: nat, logCap: int) {
  && c.id == id
  && c.f == f
  && c.logCap == logCap  // length of paxos log
}

datatype Variables = Variables(
  // Leader state
  ls: MonotonicLeaderState,
  nextSlotToPropose: nat,
  // Acceptor State
  promised: MonotonicBallotOption,
  logAcceptedVB: MonotonicVBOptionSeq,
  // Learner State
  logReceivedAccepts: MonotonicReceivedAcceptsSeq,
  logLearned: seq<Option<Value>>
) {

  ghost predicate WF(c: Constants) {
    && c.WF()
    // Leader WF
    && ls.currBal.id == c.id
    && |ls.logHighestHeardValues| == c.logCap
    && ls.f == c.f
    // Acceptor WF
    && |logAcceptedVB.vbOptSeq| == c.logCap
    && (forall slot | c.ValidSlot(slot) && logAcceptedVB.getSlot(slot).Some? :: promised.MBSome? && BalLteq(logAcceptedVB.getSlot(slot).value.b, promised.bal))
    // Learner WF
    && |logReceivedAccepts.mapSeq| == c.logCap
    && |logLearned| == c.logCap
  }

  // // My highestHeardBallot >= b
  // ghost predicate LdrHeardAtLeastAtSlot(slot: int, b: Ballot) {
  //   ls.highestHeardBallot.Some? && BalLteq(b, ls.highestHeardBallot.value)
  // }
  
  // My highestHeardBallot < b
  ghost predicate LdrHeardAtMostAtSlot(c: Constants, slot: int, b: Ballot) 
    requires WF(c)
    requires c.ValidSlot(slot)
  {
    ls.logHighestHeardValues[slot].ob.None? || BalLt(ls.logHighestHeardValues[slot].ob.value, b)
  }

  ghost predicate LdrCanPropose(c: Constants) {
    && |ls.promises| >= c.f+1
  }

  ghost function LdrValue(slot: int) : Value 
    requires 0 <= slot < |ls.logHighestHeardValues|
  {
    ls.logHighestHeardValues[slot].v
  }

  ghost function LdrReceivedPromises() : set<HostId> {
    ls.promises
  }

  // ghost predicate HasAccepted(vb: ValBal) {
  //   && acceptedVB.MVBSome?
  //   && acceptedVB.value == vb
  // }

  // ghost predicate HasAcceptedValue(v: Value) {
  //   && acceptedVB.MVBSome?
  //   && acceptedVB.value.v == v
  // }

  // ghost predicate AccHasPromisedAtLeast(b: Ballot) {
  //   && promised.MBSome?
  //   && BalLteq(b, promised.bal)
  // }

  // ghost predicate AccHasPromised(b: Ballot) {
  //   && promised.MBSome?
  //   && b == promised.bal
  // }

  ghost predicate HasLearnedValueAtSlot(v: Value, slot: nat) 
    requires 0 <= slot < |logLearned|
  {
    logLearned[slot] == Some(v)
  }    
}


/***************************************************************************************
*                                    Initialization                                    *
***************************************************************************************/

ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat, logCap: int) {
  && 0 < |grp_c|
  && (forall idx: nat | idx < |grp_c|
      :: ConstantsValid(grp_c[idx], idx, f, logCap))
}

ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat, logCap: int) {
  && 0 < f
  && GroupWFConstants(grp_c, f, logCap)
  && |grp_v| == |grp_c| == 2*f+1
  && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
}

ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat, logCap: int) 
  requires GroupWF(grp_c, grp_v, f, logCap)
{
  forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
}

ghost predicate Init(c: Constants, v: Variables) {
  && 0 < c.logCap
  // Leader init
  && v.ls.currBal == Bal(0, c.id)
  && v.ls.promises == {}
  && v.ls.logHighestHeardValues == seq(c.logCap, i => HH(None, c.preferredValue))
  && v.ls.f == c.f
  // Acceptor init
  && v.promised == MBNone
  && v.logAcceptedVB == MVBSeq(seq(c.logCap, i => None))
  // Learner init
  && v.logReceivedAccepts == RASeq(seq(c.logCap, i => map[]))
  && v.logLearned == seq(c.logCap, i => None)
}

/***************************************************************************************
*                                   Host Transitions                                   *
***************************************************************************************/

datatype Step =
  StutterStep() |
  // Leader actions
  PrepareStep() | ReceivePromiseStep() | ProposeStep() | ReceivePreemptStep() |
  // Acceptor actions
  ReceivePrepareStep() | ReceivePreparePreemptStep() | ReceiveProposeStep() | ReceiveProposePreemptStep() |
  // Learner actions
  ReceiveAcceptStep() | LearnStep(slot: int, vb: ValBal)

ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
{
  exists step :: NextStep(c, v, v', step, msgOps)
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
{
  && v.WF(c)
  && match step
    case StutterStep() => NextStutterStep(c, v, v', msgOps)
    // Leader actions
    case PrepareStep() => NextPrepareStep(c, v, v', msgOps)
    case ReceivePromiseStep() => NextReceivePromiseStep(c, v, v', msgOps)
    case ProposeStep() => NextProposeStep(c, v, v', msgOps)
    case ReceivePreemptStep() => NextReceivePreemptStep(c, v, v', msgOps)
    // Acceptor actions
    case ReceivePrepareStep() => NextPromiseStep(c, v, v', msgOps)
    case ReceivePreparePreemptStep() => NextRejectPromiseStep(c, v, v', msgOps)
    case ReceiveProposeStep() => NextAcceptStep(c, v, v', msgOps)
    case ReceiveProposePreemptStep() => NextRejectProposeStep(c, v, v', msgOps)
    // Learner actions
    case ReceiveAcceptStep() => NextReceiveAcceptStep(c, v, v', msgOps)
    case LearnStep(slot, vb) => NextLearnStep(c, v, v', vb, msgOps, slot)
}


/////////////////////////////// Leader actions

ghost predicate NextPrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.None?
  && msgOps.send.Some?
  && SendPrepare(c, v, v', msgOps.send.value)
}

// Send predicate
ghost predicate SendPrepare(c: Constants, v: Variables, v': Variables, outMsg: Message) {
  // enabling conditions
  && true
  // send message and update v'
  && outMsg == Prepare(v.ls.currBal)
  && v' == v
}

ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
  requires v.WF(c)
{
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceivePromise(c, v, v', msgOps.recv.value)
}

// Receive predicate
ghost predicate ReceivePromise(c: Constants, v: Variables, v': Variables, inMsg: Message) 
  requires v.WF(c)
{
  && inMsg.Promise?
  && var bal := inMsg.bal;
  && var acc := inMsg.acc;
  && var accLogAcceptedVB := inMsg.logAcceptedVB;
  && |accLogAcceptedVB.vbOptSeq| == c.logCap

  && bal == v.ls.currBal  // message is meant for me
  && |v.ls.promises| <= c.f
  && acc !in v.ls.promises
  
  // Do update for each slot
  && v' == v.(
    ls := v.ls.(
      logHighestHeardValues := 
        seq(c.logCap, i =>
          if 0 <= i < c.logCap then
            var doUpdate := 
                && accLogAcceptedVB.getSlot(i).Some? 
                && v.LdrHeardAtMostAtSlot(c, i, accLogAcceptedVB.getSlot(i).value.b);
            if doUpdate then HH(Some(accLogAcceptedVB.getSlot(i).value.b), accLogAcceptedVB.getSlot(i).value.v) else v.ls.logHighestHeardValues[i]
          else
            HH(None, c.preferredValue) // dummy
        ),
      promises := v.ls.promises + {acc}
    )
  )
}

ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
  requires v.WF(c)
{
  && msgOps.recv.None?
  && msgOps.send.Some?
  && SendPropose(c, v, v', msgOps.send.value)
}

// Send predicate
ghost predicate SendPropose(c: Constants, v: Variables, v': Variables, outMsg: Message) 
  requires v.WF(c)
{
  // enabling conditions
  && c.ValidSlot(v.nextSlotToPropose)
  && v.LdrCanPropose(c)
  && v.LdrHeardAtMostAtSlot(c,  v.nextSlotToPropose, v.ls.currBal)
  // send message and update v'
  && outMsg == Propose(v.nextSlotToPropose, v.ls.currBal, v.ls.logHighestHeardValues[ v.nextSlotToPropose].v)
  && v' == v.(
    nextSlotToPropose := v'.nextSlotToPropose  // non-deterministic
  )
  && c.ValidSlot(v'.nextSlotToPropose)
}

ghost predicate NextReceivePreemptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
  requires c.WF()
{
  && msgOps.recv.Some?
  && msgOps.send.None?
  && (ReceivePreempt1(c, v, v', msgOps.recv.value)
      || ReceivePreempt2(c, v, v', msgOps.recv.value))
}

// Receive predicate
// Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
ghost predicate ReceivePreempt1(c: Constants, v: Variables, v': Variables, inMsg: Message) 
  requires c.WF()
{
  && inMsg.Preempt1?
  && inMsg.ldr == c.id  // message is meant for me
  && BalLt(v.ls.currBal, inMsg.bal)
  && v' == v.(
    ls := LS(
          Bal(inMsg.bal.x+1, c.id),                // update currBal
          {},                                    // reset promises
          seq(c.logCap, i => HH(None, c.preferredValue)),              // reset highestHeardValues
          c.f
        )
  )
}

// Receive predicate
// Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
ghost predicate ReceivePreempt2(c: Constants, v: Variables, v': Variables, inMsg: Message) 
  requires c.WF()
{
  && inMsg.Preempt2?
  && inMsg.ldr == c.id  // message is meant for me
  && BalLt(v.ls.currBal, inMsg.bal)
  && v' == v.(
    ls := LS(
          Bal(inMsg.bal.x+1, c.id),                // update currBal
          {},                                    // reset promises
          seq(c.logCap, i => HH(None, c.preferredValue)),              // reset highestHeardValues
          c.f
        )
  )
}

/////////////////////////////// Acceptor actions

ghost predicate NextPromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceivePrepareSendPromise(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Send predicate
ghost predicate ReceivePrepareSendPromise(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Prepare?
  && var bal := inMsg.bal;
  && var doPromise := v.promised.MBSome? ==> BalLt(v.promised.bal, bal);
  && doPromise
  // send message and update v'
  && v' == v.(promised := MBSome(bal))
  && outMsg == Promise(bal, c.id, v.logAcceptedVB)
}

ghost predicate NextRejectPromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceivePrepareSendPreempt1(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Send predicate
ghost predicate ReceivePrepareSendPreempt1(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Prepare?
  && v.promised.MBSome?
  // send message and update v'
  && v' == v
  && outMsg == Preempt1(c.id, inMsg.bal.id, v.promised.bal)
}

ghost predicate NextAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
  requires v.WF(c)
{
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceiveProposeSendAccept(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Receive-Send predicate
ghost predicate ReceiveProposeSendAccept(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) 
  requires v.WF(c)
{
  // enabling conditions
  && inMsg.Propose?
  && var slot := inMsg.slot;
  && var bal := inMsg.bal;
  && var val := inMsg.val;
  && var doAccept := v.promised.MBSome? ==> BalLteq(v.promised.bal, bal);
  && doAccept
  && c.ValidSlot(slot)
  // update v' and specify outMsg
  && outMsg == Accept(slot, VB(val, bal), c.id) // outMsg
  && v' == v.(
      promised := MBSome(bal), 
      logAcceptedVB := v.logAcceptedVB.updateSlot(slot, Some(VB(val, bal)))
    )
}

ghost predicate NextRejectProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  // enabling conditions
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceiveProposeSendPreempt2(c, v, v', msgOps.recv.value, msgOps.send.value)
}

ghost predicate ReceiveProposeSendPreempt2(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Propose?
  && var bal := inMsg.bal;
  && var doAccept := v.promised.MBSome? ==> BalLteq(v.promised.bal, bal);
  && !doAccept
  // update v' and specify outMsg
  && outMsg == Preempt2(c.id, inMsg.bal.id, v.promised.bal)
  && v' == v  // no change
}


/////////////////////////////// Learner actions

ghost predicate NextReceiveAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
  requires v.WF(c)
{
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceiveAccept(c, v, v', msgOps.recv.value)
}

// Receive predicate
ghost predicate ReceiveAccept(c: Constants, v: Variables, v': Variables, inMsg: Message) 
  requires v.WF(c)
{
  && inMsg.Accept?
  && var slot := inMsg.slot;
  && c.ValidSlot(slot)
  && v' == v.(
    logReceivedAccepts := v.logReceivedAccepts.updateSlot(slot, UpdateReceivedAcceptsOneSlot(v.logReceivedAccepts.getSlot(slot), inMsg.vb, inMsg.acc))
  )
}

function UpdateReceivedAcceptsOneSlot(receivedAccepts: map<ValBal, set<HostId>>, vb: ValBal, acc: HostId) : (out: map<ValBal, set<HostId>>)
  // Tony: ensures clauses are exactly how I can prove to the user, and tell dafny, that 
  // data structures annotated as monotonic actually are monotonic --- cool!
  ensures vb in receivedAccepts ==> vb in out
  ensures vb in receivedAccepts ==> |receivedAccepts[vb]| <= |out[vb]|
{
  if vb in receivedAccepts then 
    UnionIncreasesCardinality(receivedAccepts[vb], {acc});
    receivedAccepts[vb := receivedAccepts[vb] + {acc}]
  else 
    receivedAccepts[vb := {acc}]
}

ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, msgOps: MessageOps, slot: int) 
  requires v.WF(c)
{
  && msgOps.recv.None?
  && msgOps.send.None?
  && c.ValidSlot(slot)
  && vb in v.logReceivedAccepts.getSlot(slot)              // enabling
  && |v.logReceivedAccepts.getSlot(slot)[vb]| >= c.f + 1   // enabling
  && v' == v.(logLearned :=
              v.logLearned[slot := Some(vb.v)]   // learn new value
      )
}

ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && v == v'
  && msgOps.send == None
  && msgOps.recv == None
}
}  // end module Host
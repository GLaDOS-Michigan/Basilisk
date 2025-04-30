include "types.dfy"
include "../lib/MonotonicityLibrary.dfy"

module Host {
import opened MonotonicityLibrary
import opened UtilitiesLibrary
import opened Types

datatype Constants = Constants(id: HostId, f: nat, preferredValue: Value)

ghost predicate ConstantsValid(c: Constants, id: HostId, f: nat) {
  && c.id == id
  && c.f == f
}

datatype Variables = Variables(
  // Leader state
  ls: MonotonicLeaderState,
  // Acceptor State
  promised: MonotonicBallotOption,
  acceptedVB: MonotonicVBOption,
  // Learner State
  receivedAccepts: MonotonicReceivedAccepts,
  learned: Option<Value>
) {

  ghost predicate WF(c: Constants) {
    // Leader WF
    && ls.currBal.id == c.id
    && ls.f == c.f
    // Acceptor WF
    && (acceptedVB.MVBSome? ==> (promised.MBSome? && BalLteq(acceptedVB.value.b, promised.bal)))
  }

  // My highestHeardBallot >= b
  ghost predicate LdrHeardAtLeast(b: Ballot) {
    ls.highestHeardBallot.Some? && BalLteq(b, ls.highestHeardBallot.value)
  }
  
  // My highestHeardBallot < b
  ghost predicate LdrHeardAtMost(b: Ballot) {
    ls.highestHeardBallot.None? || BalLt(ls.highestHeardBallot.value, b)
  }

  ghost predicate LdrCanPropose(c: Constants) {
    && |ls.promises| >= c.f+1
  }

  ghost predicate LdrCanProposeV(c: Constants, val: Value) {
    && LdrCanPropose(c)
    && ls.value == val
  }

  ghost function LdrValue() : Value {
    ls.value
  }

  ghost function LdrReceivedPromises() : set<HostId> {
    ls.promises
  }

  ghost predicate HasAccepted(vb: ValBal) {
    && acceptedVB.MVBSome?
    && acceptedVB.value == vb
  }

  ghost predicate HasAcceptedValue(v: Value) {
    && acceptedVB.MVBSome?
    && acceptedVB.value.v == v
  }

  ghost predicate AccHasPromisedAtLeast(b: Ballot) {
    && promised.MBSome?
    && BalLteq(b, promised.bal)
  }

  ghost predicate AccHasPromised(b: Ballot) {
    && promised.MBSome?
    && b == promised.bal
  }

  ghost predicate AccHasAcceptedAtLeastBal(b: Ballot) {
    && acceptedVB.MVBSome?
    && BalLteq(b, acceptedVB.value.b)
  }

  ghost predicate AccHasAcceptedAtMostBal(b: Ballot) {
    acceptedVB.MVBSome? ==> BalLt(acceptedVB.value.b, b)
  }

  ghost predicate HasLearnedValue(v: Value) {
    learned == Some(v)
  }    
}


/***************************************************************************************
*                                    Initialization                                    *
***************************************************************************************/

ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
  && 0 < |grp_c|
  && (forall idx: nat | idx < |grp_c|
      :: ConstantsValid(grp_c[idx], idx, f))
}

ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
  && 0 < f
  && GroupWFConstants(grp_c, f)
  && |grp_v| == |grp_c| == 2*f+1
  && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
}

ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
  requires GroupWF(grp_c, grp_v, f)
{
  forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
}

ghost predicate Init(c: Constants, v: Variables) {
  // Leader init
  && v.ls.currBal == Bal(0, c.id)
  && v.ls.promises == {}
  && v.ls.value == c.preferredValue
  && v.ls.highestHeardBallot == None
  && v.ls.f == c.f
  // Acceptor init
  && v.promised == MBNone
  && v.acceptedVB == MVBNone
  // Learner init
  && v.receivedAccepts == RA(map[])
  && v.learned == None
}

/***************************************************************************************
*                                   Host Transitions                                   *
***************************************************************************************/

datatype Step =
  StutterStep() |
  // Leader actions
  PrepareStep() | ReceivePromiseUpdateStep() | ReceivePromiseNoUpdateStep() | ProposeStep() | ReceivePreempt1Step() | ReceivePreempt2Step() |
  // Acceptor actions
  ReceivePrepareStep() | ReceivePreparePreemptStep() | ReceiveProposeStep() | ReceiveProposePreemptStep() |
  // Learner actions
  ReceiveAcceptStep() | LearnStep(vb: ValBal)

ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
{
  exists step :: NextStep(c, v, v', step, msgOps)
}

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
{
  match step
    case StutterStep() => NextStutterStep(c, v, v', msgOps)
    // Leader actions
    case PrepareStep() => NextPrepareStep(c, v, v', msgOps)
    case ReceivePromiseUpdateStep() => NextReceivePromiseUpdateStep(c, v, v', msgOps)
    case ReceivePromiseNoUpdateStep() => NextReceivePromiseNoUpdateStep(c, v, v', msgOps)
    case ProposeStep() => NextProposeStep(c, v, v', msgOps)
    case ReceivePreempt1Step() => NextReceivePreempt1Step(c, v, v', msgOps)
    case ReceivePreempt2Step() => NextReceivePreempt2Step(c, v, v', msgOps)
    // Acceptor actions
    case ReceivePrepareStep() => NextPromiseStep(c, v, v', msgOps)
    case ReceivePreparePreemptStep() => NextRejectPromiseStep(c, v, v', msgOps)
    case ReceiveProposeStep() => NextAcceptStep(c, v, v', msgOps)
    case ReceiveProposePreemptStep() => NextRejectProposeStep(c, v, v', msgOps)
    // Learner actions
    case ReceiveAcceptStep() => NextReceiveAcceptStep(c, v, v', msgOps)
    case LearnStep(vb) => NextLearnStep(c, v, v', vb, msgOps)
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

ghost predicate NextReceivePromiseNoUpdateStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceivePromise1(c, v, v', msgOps.recv.value)
}

// Receive predicate
ghost predicate ReceivePromise1(c: Constants, v: Variables, v': Variables, inMsg: Message) {
  && inMsg.Promise?
  && var bal := inMsg.bal;
  && var acc := inMsg.acc;
  && var vbOpt := inMsg.vbOpt;
  && bal == v.ls.currBal  // message is meant for me
  // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
  // probably simplify proof, preventing the leader from potentially equivocating
  // on its proposed value after receiving extraneous straggling promises.
  && |v.ls.promises| <= c.f
  && acc !in v.ls.promises
  && var doUpdate := 
        && vbOpt.Some? 
        && v.LdrHeardAtMost(vbOpt.value.b);
  && !doUpdate
  && v' == v.(
      ls := v.ls.( promises := v.ls.promises + {acc} )
  )
}

ghost predicate NextReceivePromiseUpdateStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceivePromise2(c, v, v', msgOps.recv.value)
}

// Receive predicate
ghost predicate ReceivePromise2(c: Constants, v: Variables, v': Variables, inMsg: Message) {
  && inMsg.Promise?
  && var bal := inMsg.bal;
  && var acc := inMsg.acc;
  && var vbOpt := inMsg.vbOpt;
  && bal == v.ls.currBal  // message is meant for me
  // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
  // probably simplify proof, preventing the leader from potentially equivocating
  // on its proposed value after receiving extraneous straggling promises.
  && |v.ls.promises| <= c.f
  && acc !in v.ls.promises
  && var doUpdate := 
        && vbOpt.Some? 
        && v.LdrHeardAtMost(vbOpt.value.b);
  && doUpdate
  && v' == v.(
      ls := v.ls.(
        value := vbOpt.value.v,
        promises := v.ls.promises + {acc},
        highestHeardBallot := Some(vbOpt.value.b)
      )
  )
}

ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.None?
  && msgOps.send.Some?
  && SendPropose(c, v, v', msgOps.send.value)
}

// Send predicate
ghost predicate SendPropose(c: Constants, v: Variables, v': Variables, outMsg: Message) {
  // enabling conditions
  && v.LdrCanProposeV(c, v.ls.value)
  && v.LdrHeardAtMost(v.ls.currBal)
  // send message and update v'
  && outMsg == Propose(v.ls.currBal, v.ls.value)
  && v' == v
}

ghost predicate NextReceivePreempt1Step(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceivePreempt1(c, v, v', msgOps.recv.value)
}

ghost predicate NextReceivePreempt2Step(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceivePreempt2(c, v, v', msgOps.recv.value)
}

// Receive predicate
// Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
ghost predicate ReceivePreempt1(c: Constants, v: Variables, v': Variables, inMsg: Message) {
  && inMsg.Preempt1?
  && inMsg.ldr == c.id  // message is meant for me
  && BalLt(v.ls.currBal, inMsg.bal)
  && v' == v.(
    ls := LS(
          Bal(inMsg.bal.x+1, c.id),   // update currBal
          c.preferredValue,         // reset value
          {},                       // reset promises
          None,                     // reset highestHeardBallot
          c.f
        )
  )
}

// Receive predicate
// Preempt1 and Preempt2 comes from Kondo's restriction of one message type per send action
ghost predicate ReceivePreempt2(c: Constants, v: Variables, v': Variables, inMsg: Message) {
  && inMsg.Preempt2?
  && inMsg.ldr == c.id  // message is meant for me
  && BalLt(v.ls.currBal, inMsg.bal)
  && v' == v.(
    ls := LS(
          Bal(inMsg.bal.x+1, c.id),   // update currBal
          c.preferredValue,         // reset value
          {},                       // reset promises
          None,                     // reset highestHeardBallot
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
  && v' == v.(promised := MBSome(inMsg.bal))
  && outMsg == Promise(bal, c.id, v.acceptedVB.ToOption())
}

ghost predicate NextRejectPromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.recv.value.Prepare?
  && msgOps.send.Some?
  && ReceivePrepareSendPreempt1(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Send predicate
ghost predicate ReceivePrepareSendPreempt1(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Prepare?
  && var bal := inMsg.bal;
  && v.promised.MBSome?
  && var doPromise := BalLt(v.promised.bal, bal);
  && !doPromise
  // send message and update v'
  && v' == v
  && outMsg == Preempt1(c.id, inMsg.bal.id, v.promised.bal)
}

// Note that this step contains both receive and send
ghost predicate NextAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  // enabling conditions
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceiveProposeSendAccept(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Receive-Send predicate
ghost predicate ReceiveProposeSendAccept(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Propose?
  // update v' and specify outMsg
  && var bal := inMsg.bal;
  && var val := inMsg.val;
  && var doAccept := v.promised.MBSome? ==> BalLteq(v.promised.bal, bal);
  && doAccept
  && outMsg == Accept(VB(val, bal), c.id) // outMsg
  && v' == v.(
      promised := MBSome(bal), 
      acceptedVB := MVBSome(VB(val, bal)))
}

// Note that this step contains both receive and send
ghost predicate NextRejectProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  // enabling conditions
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceiveProposeSendPreempt2(c, v, v', msgOps.recv.value, msgOps.send.value)
}

ghost predicate ReceiveProposeSendPreempt2(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Propose?
  && v.promised.MBSome?
  && var bal := inMsg.bal;
  && var doAccept := BalLteq(v.promised.bal, bal);
  && !doAccept
  // update v' and specify outMsg
  && outMsg == Preempt2(c.id, inMsg.bal.id, v.promised.bal)
  && v' == v  // no change
}


/////////////////////////////// Learner actions

function UpdateReceivedAccepts(receivedAccepts: MonotonicReceivedAccepts, 
  vb: ValBal, acc: HostId) : (out: MonotonicReceivedAccepts)
  // Tony: ensures clauses are exactly how I can prove to the user, and tell dafny, that 
  // data structures annotated as monotonic actually are monotonic --- cool!
  ensures vb in receivedAccepts.m ==> vb in out.m
  ensures vb in receivedAccepts.m ==> |receivedAccepts.m[vb]| <= |out.m[vb]|
{
  if vb in receivedAccepts.m then 
    UnionIncreasesCardinality(receivedAccepts.m[vb], {acc});
    RA(receivedAccepts.m[vb := receivedAccepts.m[vb] + {acc}])
  else 
    RA(receivedAccepts.m[vb := {acc}])
}

ghost predicate NextReceiveAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.None?
  && ReceiveAccept(c, v, v', msgOps.recv.value)
}

// Receive predicate
ghost predicate ReceiveAccept(c: Constants, v: Variables, v': Variables, inMsg: Message) {
  && inMsg.Accept?
  && v' == v.(
    receivedAccepts := UpdateReceivedAccepts(v.receivedAccepts, inMsg.vb, inMsg.acc)
  )
}

ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, msgOps: MessageOps) {
  && msgOps.recv.None?
  && msgOps.send.None?
  && vb in v.receivedAccepts.m              // enabling
  && |v.receivedAccepts.m[vb]| >= c.f + 1   // enabling
  && v' == v.(learned := Some(vb.v))        // learn new value
}

ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && v == v'
  && msgOps.send == None
  && msgOps.recv == None
}
}  // end module Host
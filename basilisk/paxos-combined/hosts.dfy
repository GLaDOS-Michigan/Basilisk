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
  receivedPromisesAndValue: MonotonicPromisesAndValue,
  highestHeardBallot: MonotonicNatOption,
  // Acceptor State
  promised: MonotonicNatOption,
  acceptedVB: MonotonicVBOption,
  // Learner State
  receivedAccepts: MonotonicReceivedAccepts,
  learned: Option<Value>
) {

  ghost predicate WF(c: Constants) {
    // Leader WF
    && receivedPromisesAndValue.f == c.f
    // Acceptor WF
    && (acceptedVB.MVBSome? ==> (promised.MNSome? && acceptedVB.value.b <= promised.value))
  }

  // My highestHeardBallot >= b
  ghost predicate LdrHeardAtLeast(b: HostId) {
    highestHeardBallot.MNSome? && highestHeardBallot.value >= b
  }
  
  // My highestHeardBallot < b
  ghost predicate LdrHeardAtMost(b: HostId) {
    highestHeardBallot.MNNone? || highestHeardBallot.value < b
  }

  ghost predicate LdrCanPropose(c: Constants) {
    && |receivedPromisesAndValue.promises| >= c.f+1
  }

  ghost predicate LdrCanProposeV(c: Constants, val: Value) {
    && LdrCanPropose(c)
    && receivedPromisesAndValue.value == val
  }

  ghost function LdrValue() : Value {
    receivedPromisesAndValue.value
  }

  ghost function LdrReceivedPromises() : set<HostId> {
    receivedPromisesAndValue.promises
  }

  ghost predicate HasAccepted(vb: ValBal) {
    && acceptedVB.MVBSome?
    && acceptedVB.value == vb
  }

  ghost predicate HasAcceptedValue(v: Value) {
    && acceptedVB.MVBSome?
    && acceptedVB.value.v == v
  }

  ghost predicate AccHasPromisedAtLeast(b: HostId) {
    && promised.MNSome?
    && b <= promised.value
  }

  ghost predicate AccHasPromised(b: HostId) {
    && promised.MNSome?
    && b == promised.value
  }

  ghost predicate AccHasAcceptedAtLeastBal(b: HostId) {
    && acceptedVB.MVBSome?
    && b <= acceptedVB.value.b
  }

  ghost predicate AccHasAcceptedAtMostBal(b: HostId) {
    acceptedVB.MVBSome? ==> acceptedVB.value.b < b
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
  && v.receivedPromisesAndValue == PV({}, c.preferredValue, c.f)
  && v.highestHeardBallot == MNNone
  // Acceptor init
  && v.promised == MNNone
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
  PrepareStep() | ReceivePromiseUpdateStep() | ReceivePromiseNoUpdateStep() | ProposeStep() |
  // Acceptor actions
  ReceivePrepareStep() | MaybeAcceptStep() |
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
    case ReceivePromiseUpdateStep => NextReceivePromiseUpdateStep(c, v, v', msgOps)
    case ReceivePromiseNoUpdateStep => NextReceivePromiseNoUpdateStep(c, v, v', msgOps)
    case ProposeStep() => NextProposeStep(c, v, v', msgOps)
    // Acceptor actions
    case ReceivePrepareStep() => NextPromiseStep(c, v, v', msgOps)
    case MaybeAcceptStep() => NextAcceptStep(c, v, v', msgOps)
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
ghost predicate SendPrepare(c: Constants, v: Variables, v': Variables, msg: Message) {
  // enabling conditions
  && true
  // send message and update v'
  && msg == Prepare(c.id)
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
  && bal == c.id  // message is meant for me
  // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
  // probably simplify proof, preventing the leader from potentially equivocating
  // on its proposed value after receiving extraneous straggling promises.
  && |v.receivedPromisesAndValue.promises| <= c.f
  && acc !in v.receivedPromisesAndValue.promises
  && var doUpdate := 
        && vbOpt.Some? 
        && v.LdrHeardAtMost(vbOpt.value.b);
  && !doUpdate
    && v' == v.(
        receivedPromisesAndValue := 
          v.receivedPromisesAndValue.(promises 
            := v.receivedPromisesAndValue.promises + {acc})
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
  && bal == c.id  // message is meant for me
  // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
  // probably simplify proof, preventing the leader from potentially equivocating
  // on its proposed value after receiving extraneous straggling promises.
  && |v.receivedPromisesAndValue.promises| <= c.f
  && acc !in v.receivedPromisesAndValue.promises
  && var doUpdate := 
        && vbOpt.Some? 
        && v.LdrHeardAtMost(vbOpt.value.b);
  && doUpdate
    && v' == v.(
              receivedPromisesAndValue := 
                v.receivedPromisesAndValue.(
                  promises := v.receivedPromisesAndValue.promises + {acc},
                  value := vbOpt.value.v),
              highestHeardBallot := MNSome(vbOpt.value.b)
            )
}

ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.None?
  && msgOps.send.Some?
  && SendPropose(c, v, v', msgOps.send.value)
}

// Send predicate
ghost predicate SendPropose(c: Constants, v: Variables, v': Variables, msg: Message) {
  // enabling conditions
  && v.LdrCanProposeV(c, v.receivedPromisesAndValue.value)
  && v.LdrHeardAtMost(c.id)
  // send message and update v'
  && msg == Propose(c.id, v.receivedPromisesAndValue.value)
  && v' == v
}


/////////////////////////////// Acceptor actions

ghost predicate NextPromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceivePrepareSendPromise(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Receive-and-Send predicate
ghost predicate ReceivePrepareSendPromise(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Prepare?
  && var bal := inMsg.bal;
  && var doPromise := v.promised.MNSome? ==> v.promised.value < bal;
  && doPromise
  // send message and update v'
  && v' == v.(promised := MNSome(inMsg.bal))
  && outMsg == Promise(inMsg.bal, c.id, v.acceptedVB.ToOption())
}

// Note that this step contains both receive and send
ghost predicate NextAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
  && msgOps.recv.Some?
  && msgOps.send.Some?
  && ReceiveProposeSendAccept(c, v, v', msgOps.recv.value, msgOps.send.value)
}

// Receive-and-Send predicate
ghost predicate ReceiveProposeSendAccept(c: Constants, v: Variables, v': Variables, inMsg: Message, outMsg: Message) {
  // enabling conditions
  && inMsg.Propose?
  // update v' and specify outMsg
  && var bal := inMsg.bal;
  && var val := inMsg.val;
  && var doAccept := (v.promised.MNSome? ==> v.promised.value <= bal);
  && doAccept
  && outMsg == Accept(VB(val, bal), c.id) // outMsg
  && v' == v.(
        promised := MNSome(bal), 
        acceptedVB := MVBSome(VB(val, bal)))
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
include "types.dfy"
include "../../lib/MonotonicityLibrary.dfy"

/***************************************************************************************
*                                      Leader Host                                     *
***************************************************************************************/

module LeaderHost {
  import opened MonotonicityLibrary
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LeaderId, f: nat, preferredValue: Value)

  ghost predicate ConstantsValidForLeader(c: Constants, id: LeaderId, f: nat) {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(
    receivedPromisesAndValue: MonotonicPromisesAndValue,
    highestHeardBallot: MonotonicNatOption  // holds LeaderId
  ) {

    ghost predicate WF(c: Constants) {
      receivedPromisesAndValue.f == c.f
    }

    // My highestHeardBallot >= b
    ghost predicate HeardAtLeast(b: LeaderId) {
      highestHeardBallot.MNSome? && highestHeardBallot.value >= b
    }
    
    // My highestHeardBallot < b
    ghost predicate HeardAtMost(b: LeaderId) {
      highestHeardBallot.MNNone? || highestHeardBallot.value < b
    }

    ghost predicate CanPropose(c: Constants) {
      && |receivedPromisesAndValue.promises| >= c.f+1
    }

    ghost predicate CanProposeV(c: Constants, val: Value) {
      && CanPropose(c)
      && receivedPromisesAndValue.value == val
    }

    ghost function Value() : Value {
      receivedPromisesAndValue.value
    }

    ghost function ReceivedPromises() : set<AcceptorId> {
      receivedPromisesAndValue.promises
    }
  } // end datatype Variables (Leader)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLeader(grp_c[idx], idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF(grp_c[i]))
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedPromisesAndValue == PV({}, c.preferredValue, c.f)
    && v.highestHeardBallot == MNNone
  }

  datatype Step =
    PrepareStep() | ReceiveStep() | ProposeStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case PrepareStep => NextPrepareStep(c, v, v', msgOps)
      case ReceiveStep => NextReceivePromiseStep(c, v, v', msgOps)
      case ProposeStep => NextProposeStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

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

  ghost predicate NextReceivePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && ReceivePromise(c, v, v', msgOps.recv.value)
  }

  // Receive predicate
  ghost predicate ReceivePromise(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg.Promise?
    && var bal := msg.bal;
    && var acc := msg.acc;
    && var vbOpt := msg.vbOpt;
    && bal == c.id  // message is meant for me
    // Enabling condition that I don't yet have a quorum. Not a safety issue, but can
    // probably simplify proof, preventing the leader from potentially equivocating
    // on its proposed value after receiving extraneous straggling promises.
    && |v.receivedPromisesAndValue.promises| <= c.f
    && acc !in v.receivedPromisesAndValue.promises
    && var doUpdate := 
          && vbOpt.Some? 
          && v.HeardAtMost(vbOpt.value.b);
    v' == v.(
              receivedPromisesAndValue := PV(v.receivedPromisesAndValue.promises + {acc}, if doUpdate then vbOpt.value.v else v.receivedPromisesAndValue.value, c.f),
              highestHeardBallot := if doUpdate then MNSome(vbOpt.value.b) else v.highestHeardBallot
            )
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceivePromiseTrigger(c: Constants, v: Variables, acc: AcceptorId) {
    && acc in v.receivedPromisesAndValue.promises
  }

  ghost predicate NextProposeStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.Some?
    && SendPropose(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendPropose(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.CanProposeV(c, v.receivedPromisesAndValue.value)
    && v.HeardAtMost(c.id)
    // send message and update v'
    && msg == Propose(c.id, v.receivedPromisesAndValue.value)
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && v == v'
    && msgOps.send == None
    && msgOps.recv == None
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LeaderHost


/***************************************************************************************
*                                     Acceptor Host                                    *
***************************************************************************************/

module AcceptorHost {
  import opened MonotonicityLibrary
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: AcceptorId)

  ghost predicate ConstantsValidForAcceptor(c: Constants, id: AcceptorId) {
    && c.id == id
  }

  datatype PendingPrepare = Prepare(bal:LeaderId)

  datatype Variables = Variables(
    pendingPrepare: Option<PendingPrepare>,
    promised: MonotonicNatOption,   // contains LeaderId
    acceptedVB: MonotonicVBOption
  ) {

    ghost predicate WF() {
      acceptedVB.MVBSome? ==> (promised.MNSome? && acceptedVB.value.b <= promised.value)
    }

    ghost predicate HasAccepted(vb: ValBal) {
      && acceptedVB.MVBSome?
      && acceptedVB.value == vb
    }

    ghost predicate HasAcceptedValue(v: Value) {
      && acceptedVB.MVBSome?
      && acceptedVB.value.v == v
    }

    ghost predicate HasPromisedAtLeast(b: LeaderId) {
      && promised.MNSome?
      && b <= promised.value
    }

    ghost predicate HasPromised(b: LeaderId) {
      && promised.MNSome?
      && b == promised.value
    }

    ghost predicate HasAcceptedAtLeastBal(b: LeaderId) {
      && acceptedVB.MVBSome?
      && b <= acceptedVB.value.b
    }

    ghost predicate HasAcceptedAtMostBal(b: LeaderId) {
      acceptedVB.MVBSome? ==> acceptedVB.value.b < b
    }
  } // end datatype Variables (acceptor)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForAcceptor(grp_c[idx], idx))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && GroupWFConstants(grp_c)
    && |grp_v| == |grp_c| == 2*f+1
    && (forall i | 0 <= i < |grp_c| :: grp_v[i].WF())
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.promised == MNNone
    && v.acceptedVB == MVBNone
    && v.pendingPrepare == None
  }

  datatype Step =
    ReceivePrepareStep() 
    | MaybePromiseStep() 
    | MaybeAcceptStep() 
    | BroadcastAcceptedStep() 
    | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceivePrepareStep => NextReceivePrepareStep(c, v, v', msgOps)
      case MaybePromiseStep => NextMaybePromiseStep(c, v, v', msgOps)
      case MaybeAcceptStep => NextMaybeAcceptStep(c, v, v', msgOps)
      case BroadcastAcceptedStep => NextBroadcastAcceptedStep(c, v, v', msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  ghost predicate NextReceivePrepareStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && msgOps.recv.value.Prepare?
    && v.pendingPrepare.None?
    && v' == v.(
      pendingPrepare := Some(PendingPrepare.Prepare(msgOps.recv.value.bal))
    )
  }

  ghost predicate NextMaybePromiseStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.None?
    && v.pendingPrepare.Some?
    && var bal := v.pendingPrepare.value.bal;
    && var doPromise := v.promised.MNSome? ==> v.promised.value < bal;
    && if doPromise then
          && msgOps.send.Some?
          && SendPromise(c, v, v', msgOps.send.value)
        else
          && v' == v.(pendingPrepare := None)
          && msgOps.send == None
  }

  // Send predicate
  ghost predicate SendPromise(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.pendingPrepare.Some?
    && var bal := v.pendingPrepare.value.bal;
    && var doPromise := v.promised.MNSome? ==> v.promised.value < bal;
    && doPromise
    // send message and update v'
    && v' == v.(
            promised := MNSome(bal),
            pendingPrepare := None)
    && msg == Promise(bal, c.id, v.acceptedVB.ToOption())
  }

  ghost predicate NextMaybeAcceptStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.Some?
    && msgOps.recv.value.Propose?
    && v.pendingPrepare.None?
    && var bal := msgOps.recv.value.bal;
    && var val := msgOps.recv.value.val;
    && var doAccept := (v.promised.MNSome? ==> v.promised.value <= bal);
    &&  if doAccept then
          && msgOps.send == Some(Accept(VB(val, bal), c.id))
          && v' == v.(
                promised := MNSome(bal), 
                acceptedVB := MVBSome(VB(val, bal)))
        else
          && v' == v
          && msgOps.send.None?
  }

  ghost predicate NextBroadcastAcceptedStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv == None
    && msgOps.send.Some?
    && SendAccept(c, v, v', msgOps.send.value)
  }

  // Send predicate
  ghost predicate SendAccept(c: Constants, v: Variables, v': Variables, msg: Message) {
    // enabling conditions
    && v.pendingPrepare.None?
    && v.acceptedVB.MVBSome?
    && v.promised == MNSome(v.acceptedVB.value.b)
    // send message and update v'
    && msg == Accept(v.acceptedVB.value, c.id)
    && v' == v
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.send == None
    && msgOps.recv == None
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }

  lemma UpdateReceiveAcceptedStep(c: Constants, v: Variables, v': Variables, 
    step: Step, msgOps: MessageOps)
    requires NextStep(c, v, v', step, msgOps)
    requires !step.MaybeAcceptStep?
    ensures v'.acceptedVB == v.acceptedVB
  {}
}  // end module AcceptorHost


/***************************************************************************************
*                                     Learner Host                                     *
***************************************************************************************/

module LearnerHost {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: LearnerId, f: nat)

  ghost predicate ConstantsValidForLearner(c: Constants, id: LearnerId, f: nat) {
    && c.id == id
    && c.f == f
  }

  datatype Variables = Variables(
    // maps ValBal to acceptors that accepted such pair
    receivedAccepts: MonotonicReceivedAccepts,
    learned: Option<Value>
  ) {
    
    ghost predicate HasLearnedValue(v: Value) {
      learned == Some(v)
    }
  } // end datatype Variables (Learner)

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < |grp_c|
    && (forall idx: nat | idx < |grp_c|
        :: ConstantsValidForLearner(grp_c[idx], idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.receivedAccepts == RA(map[])
    && v.learned == None
  }

  datatype Step =
    ReceiveStep() | LearnStep(vb: ValBal) | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case ReceiveStep => NextReceiveAcceptStep(c, v, v', msgOps)
      case LearnStep(vb) => NextLearnStep(c, v, v', vb, msgOps)
      case StutterStep => NextStutterStep(c, v, v', msgOps)
  }

  function UpdateReceivedAccepts(receivedAccepts: MonotonicReceivedAccepts, 
    vb: ValBal, acc: AcceptorId) : (out: MonotonicReceivedAccepts)
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
  ghost predicate ReceiveAccept(c: Constants, v: Variables, v': Variables, msg: Message) {
    && msg.Accept?
    && v' == v.(
      receivedAccepts := UpdateReceivedAccepts(v.receivedAccepts, msg.vb, msg.acc)
    )
  }

  // Receive predicate trigger
  // First 2 arguments are mandatory. Second argument identifies target host. 
  ghost predicate ReceiveAcceptTrigger(c: Constants, v: Variables, acc: AcceptorId, vb: ValBal) {
    && vb in v.receivedAccepts.m
    && acc in v.receivedAccepts.m[vb]
  }

  ghost predicate NextLearnStep(c: Constants, v: Variables, v': Variables, vb: ValBal, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && vb in v.receivedAccepts.m              // enabling
    && |v.receivedAccepts.m[vb]| >= c.f + 1   // enabling
    && v' == v.(learned := Some(vb.v))        // learn new value
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
    && msgOps.recv.None?
    && msgOps.send.None?
    && v' == v
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}  // end module LearnerHost
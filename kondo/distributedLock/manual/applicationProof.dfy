include "spec.dfy"

module ToylockProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  ghost predicate MsgInFlight(c: Constants, v: Variables, msg: Message) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && c.ValidIdx(msg.dst) 
    && msg.epoch > v.hosts[msg.dst].myEpoch
  }

  ghost predicate AtMostOneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall m1, m2 | 
      && m1 in v.network.sentMsgs && m2 in v.network.sentMsgs 
      && MsgInFlight(c, v, m1) && MsgInFlight(c, v, m2)
    ::
      m1 == m2
  }

  ghost predicate NoneHasLock(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx | c.ValidIdx(idx) :: !HoldsLock(c, v, idx)
  }
  

  ghost predicate HasLockImpliesNoneInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (!NoneHasLock(c, v))
    ==>
    (forall msg | msg in v.network.sentMsgs :: !MsgInFlight(c, v, msg))
  }

  // Protocol bundle: 2 clauses in total
  ghost predicate ProtocolInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && AtMostOneInFlight(c, v)
    && HasLockImpliesNoneInFlight(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && ProtocolInv(c, v)
    && Safety(c, v)
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  {}

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    assert AtMostOneInFlight(c, v');
    assert HasLockImpliesNoneInFlight(c, v');
    assert Safety(c, v');
  }
}


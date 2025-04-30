include "messageInvariants.dfy"

module LockServerProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  import opened MessageInvariants

/***************************************************************************************
*                                   Definitions                                        *
***************************************************************************************/

  ghost predicate LockInFlight(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    exists msg :: LockInFlightByMessage(c, v, msg)
  }

  ghost predicate LockInFlightByMessage(c: Constants, v: Variables, msg: Message) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && ((0 <= msg.Dst() < |c.clients| &&
          ClientHost.UniqueKeyInFlightForHost(c.clients[msg.Dst()], v.clients[msg.Dst()], 0, msg)
        )
        || (0 <= msg.Dst() < |c.server| &&
            ServerHost.UniqueKeyInFlightForHost(c.server[msg.Dst()], v.server[msg.Dst()], 0, msg)
        )
    )
  }

  ghost predicate NoClientOwnsLock(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.clients| 
    :: 
    !v.clients[idx].hasLock
  }

  ghost predicate NoServerOwnsLock(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.server|
    :: 

    !v.server[idx].hasLock
  }

  ghost predicate NoHostOwnsLock(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    && NoClientOwnsLock(c, v)
    && NoServerOwnsLock(c, v)
  }

/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/


  ghost predicate AtMostOneInFlightMessage(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall m1, m2 | LockInFlightByMessage(c, v, m1) && LockInFlightByMessage(c, v, m2)
    :: m1 == m2
  }

  ghost predicate HostOwnsLockImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    !NoHostOwnsLock(c, v) ==> !LockInFlight(c, v)
  }

  ghost predicate AtMostOneLockHolderClients(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2| 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && v.clients[h1].hasLock
      && v.clients[h2].hasLock
    ::
      && h1 == h2
  }

  ghost predicate AtMostOneLockHolderServers(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2 | 
      && 0 <= h1 < |c.server|
      && 0 <= h2 < |c.server|
      && v.server[h1].hasLock
      && v.server[h2].hasLock
    ::
      && h1 == h2
  }

  ghost predicate ServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables)
  requires v.WF(c)
  {
    v.server[0].hasLock ==> NoClientOwnsLock(c, v)
  }
  
  // Protocol bundle: 5 clauses in total
  ghost predicate ProtocolInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && AtMostOneInFlightMessage(c, v)
    && AtMostOneLockHolderClients(c, v)
    && AtMostOneLockHolderServers(c, v)
    && HostOwnsLockImpliesNotInFlight(c, v)
    && ServerOwnsLockImpliesNoClientsOwnsLock(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && MessageInv(c, v)
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
  {
    InitImpliesMessageInv(c, v);
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    MessageInvInductive(c, v, v');
    InvNextAtMostOneInFlightMessage(c, v, v');
    InvNextHostOwnsLockImpliesNotInFlight(c, v, v');
    InvNextAtMostOneLockHolderClients(c, v, v');
    InvNextAtMostOneLockHolderServers(c, v, v');
    InvNextServerOwnsLockImpliesNoClientsOwnsLock(c, v, v');
    AtMostOneLockOwnerImpliesSafety(c, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma AtMostOneLockOwnerImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneLockHolderClients(c, v)
  ensures Safety(c, v)
{}

lemma InvNextAtMostOneInFlightMessage(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlightMessage(c, v')
{
  forall m1, m2 | LockInFlightByMessage(c, v', m1) && LockInFlightByMessage(c, v', m2) 
  ensures m1 == m2
  {
    if m1 != m2 {
      if LockInFlightByMessage(c, v, m1) {
        assert !LockInFlightByMessage(c, v, m2);
      } else {
        assert LockInFlightByMessage(c, v, m2);
      }
    }
  }
}

lemma InvNextHostOwnsLockImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsLockImpliesNotInFlight(c, v')
{
  if !NoHostOwnsLock(c, v') && LockInFlight(c, v'){
    var msg :| LockInFlightByMessage(c, v', msg);
    if msg in v.network.sentMsgs {
      assert LockInFlightByMessage(c, v, msg);
      var dsStep :| NextStep(c, v, v', dsStep);
      assert dsStep.msgOps.recv.value == msg by {
        if dsStep.msgOps.recv.value != msg {
          var m' := dsStep.msgOps.recv.value;
          assert !LockInFlightByMessage(c, v, m');
        }
      }
    }
  }
}

lemma InvNextAtMostOneLockHolderClients(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneLockHolderClients(c, v')
{
  forall h1, h2 | 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && v'.clients[h1].hasLock
      && v'.clients[h2].hasLock
  ensures
     && h1 == h2
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if h1 != h2 {
      if v'.clients[h2].hasLock {
        assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);  
        assert false;
      }
      if v'.clients[h1].hasLock {
        assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);  
        assert false;
      }
    } 
  }
}

lemma InvNextAtMostOneLockHolderServers(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneLockHolderServers(c, v')
{
  forall h1, h2 | 
      && 0 <= h1 < |c.server|
      && 0 <= h2 < |c.server|
      && v'.server[h1].hasLock
      && v'.server[h2].hasLock
  ensures
     && h1 == h2
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if h1 != h2 {
      if v'.server[h2].hasLock {
        assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);  
        assert false;
      }
      if v'.server[h1].hasLock {
        assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);  
        assert false;
      }
    }
  }
}

lemma InvNextServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerOwnsLockImpliesNoClientsOwnsLock(c, v')
{
  if v'.server[0].hasLock {
    var dsStep :| NextStep(c, v, v', dsStep);
    var idx :| 0 <= idx < |c.server| && v'.server[idx].hasLock;
    if v.server[idx].hasLock {
      assert !LockInFlight(c, v);
      if !NoClientOwnsLock(c, v') {
        assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);
        assert false;
      }
    } else {
      assert LockInFlightByMessage(c, v, dsStep.msgOps.recv.value);
    }    
  }
}

} // end module LockServerProof
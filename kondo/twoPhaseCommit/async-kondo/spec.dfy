// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: The Commit decision can only be reached if all processes prefer Yes.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened UtilitiesLibrary
  import opened MonotonicityLibrary
  import opened DistributedSystem

  // AC-1: All processes that reach a decision reach the same decision as the coordinator.
  ghost predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // auto triggers: {v.Last().participants[i]}, {PartipantHasDecided(c, v.Last(), i)}, {c.ValidParticipantId(i)}
    forall i: HostId
    {:trigger v.Last().participants[i]} {:trigger PartipantHasDecided(c, v.Last(), i)} {:trigger c.ValidParticipantId(i)} 
    :: (c.ValidParticipantId(i) && PartipantHasDecided(c, v.Last(), i)
      ==> v.Last().GetCoordinator(c).decision == v.Last().participants[i].decision)
  }

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
    CoordinatorDecidedCommit(c, v.Last())
    ==>
    AllPreferYes(c)
  }

  // This one is easier to prove
  ghost predicate AC3Contrapos(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (!AllPreferYes(c) && CoordinatorHasDecided(c, v.Last()))
    ==>
    CoordinatorDecidedAbort(c, v.Last())
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (AllPreferYes(c) && CoordinatorHasDecided(c, v.Last()))
    ==> 
    CoordinatorDecidedCommit(c, v.Last())
  }

  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }


  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/


  ghost predicate PartipantHasDecided(c: Constants, h: Hosts, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision.WOSome?
  }

  ghost predicate ParticipantDecidedCommit(c: Constants, h: Hosts, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision == WOSome(Commit)
  }

  ghost predicate ParticipantDecidedAbort(c: Constants, h: Hosts, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision == WOSome(Abort)
  }

  ghost predicate CoordinatorHasDecided(c: Constants, h: Hosts) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision.WOSome?
  }

  ghost predicate CoordinatorDecidedCommit(c: Constants, h: Hosts) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision == WOSome(Commit)
  }

  ghost predicate CoordinatorDecidedAbort(c: Constants, h: Hosts) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision == WOSome(Abort)
  }

  ghost function GetParticipantPreference(c: Constants, i: int) : Vote
    requires c.WF()
    requires 0 <= i < |c.participants|
  {
    c.participants[i].preference
  }

  ghost predicate AllPreferYes(c: Constants) 
    requires c.WF()
  {
    forall j: HostId | c.ValidParticipantId(j) :: c.participants[j].preference == Yes
  }
}

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

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  ghost predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall i: HostId | c.ValidParticipantId(i) && ParticipantDecidedCommit(c, v, i)
    :: AllPreferYes(c)
  }

  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    SafetyAC3(c, v)
  }


  /***************************************************************************************
  *                                      Utils                                           *
  ***************************************************************************************/


  ghost predicate PartipantHasDecided(c: Constants, v: Variables, pidx: HostId) 
    requires v.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    v.participants[pidx].decision.WOSome?
  }

  ghost predicate ParticipantDecidedCommit(c: Constants, v: Variables, pidx: HostId) 
    requires v.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    v.participants[pidx].decision == WOSome(Commit)
  }

  ghost predicate CoordinatorHasDecided(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    v.GetCoordinator(c).decision.WOSome?
  }

  ghost predicate CoordinatorDecidedCommit(c: Constants, v: Variables) 
    requires v.WF(c)
  {
    v.GetCoordinator(c).decision == WOSome(Commit)
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

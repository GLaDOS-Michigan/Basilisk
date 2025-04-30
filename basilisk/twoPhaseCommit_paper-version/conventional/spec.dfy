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
    forall pidx | c.ValidParticipantId(pidx) && ParticipantDecidedCommit(c, v, pidx)
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


  ghost predicate PartipantHasDecided(c: Constants, h: Variables, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision.Some?
  }

  ghost predicate ParticipantDecidedCommit(c: Constants, h: Variables, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision == Some(Commit)
  }

  ghost predicate ParticipantDecidedAbort(c: Constants, h: Variables, pidx: HostId) 
    requires h.WF(c)
    requires c.ValidParticipantId(pidx)
  {
    h.participants[pidx].decision == Some(Abort)
  }

  ghost predicate CoordinatorHasDecided(c: Constants, h: Variables) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision.Some?
  }

  ghost predicate CoordinatorDecidedCommit(c: Constants, h: Variables) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision == Some(Commit)
  }

  ghost predicate CoordinatorDecidedAbort(c: Constants, h: Variables) 
    requires h.WF(c)
  {
    h.GetCoordinator(c).decision == Some(Abort)
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

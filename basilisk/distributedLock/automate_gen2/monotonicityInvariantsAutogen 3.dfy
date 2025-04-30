/// This file is auto-generated from /Users/nudzhang/Documents/2025/osdi/artifact.nosync/basilisk/distributedLock/automate_gen2/distributedSystem.dfy
/// Generated 04/29/2025 09:11 Pacific Standard Time
include "spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate MonotonicityInv(c: Constants, v: Variables)
{
  && v.WF(c)
}

// Base obligation
lemma InitImpliesMonotonicityInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MonotonicityInv(c, v)
{
}

// Inductive obligation
lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)
  requires MonotonicityInv(c, v)
  requires Next(c, v, v')
  ensures MonotonicityInv(c, v')
{
  VariableNextProperties(c, v, v');
}

} // end module MonotonicityInvariants

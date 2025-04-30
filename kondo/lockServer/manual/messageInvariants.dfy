include "spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

ghost predicate ValidMessages(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall msg | msg in v.network.sentMsgs
    :: && (if msg.Release? then c.ValidClientIdx(msg.Src()) else msg.Src() == 0)
       && (if msg.Grant? then c.ValidClientIdx(msg.Dst()) else msg.Dst() == 0)
  }


// Message bundle: 2 clauses in total
ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidMessages(c, v)  // 2
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')
{}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/


} // end module MessageInvariants
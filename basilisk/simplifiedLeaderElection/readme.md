# Simplified Leader Election Protocol

Hosts can receive and send messages in the same step.

## Simplified Leader Election with Stronger Monotonicity Properties

During the 14 May 2024 Linear Dist meeting, it was postulated that Kondo-style
Regular Invariants alone were insufficient in implying all host invariants. In particular,
there may be issues with host invariants that only talk about the local state of a single
host, that transitioned through some spontaneous local action. This is because
the relation between the pre- and post-states of such an action cannot be captured by
Kondo's Send and Receive invariants.

This postulation is confirmed by the need to state `IsLeaderImpliesHasQuorum` as a Protocol
Invariant in the kondo-baseline version, which uses exactly those Regular Invariants that
can be generated in Kondo. This invariant is needed because it is not possible to prove
directly from the Regular Invariants that for any host state `v`, if `v` is the leader then
`v` must have a quorum of votes -- the logical connection between `isLeader` and having a
quorum is missing.

The strong-mono version addresses this problem with the new technique of introducing more
advanced monotonicity invariants. Basically, it says that for any monotonic variables,
if its current value is not the same as its initial value, then there must be a step in
the history where it changed to its current value. E.g.

```cs
// If a monotonic structure is not the same as it's initial value, then there is a step where
// it obtained its current value
ghost predicate {:opaque} HostIsLeaderExistsWitness(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.hosts|
    && v.History(i).hosts[idx].isLeader != v.History(0).hosts[idx].isLeader
  ::
    (exists j, step, msgOps::
      && v.ValidHistoryIdxStrict(j)
      && (v.History(j).hosts[idx].isLeader != v.History(j+1).hosts[idx].isLeader)
      && (v.History(j+1).hosts[idx].isLeader == v.History(i).hosts[idx].isLeader)
      && Host.NextStep(c.hosts[idx], v.History(j).hosts[idx], v.History(j+1).hosts[idx], step, msgOps)
    )
}
```

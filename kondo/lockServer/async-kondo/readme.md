# Notes

Generates async proof from sync proof.

## Commands

Generate monotonicity and message invariants:

```bash
./local-dafny/Scripts/dafny /msgInvs /ownerInvs distributedSystem.dfy
```

Generate async draft proof:

```bash
./local-dafny/Scripts/dafny /genAsyncProof ../centralized/applicationProof.dfy
```

The following lemmas are manually added or modified to complete the proof:

```dafny
// modified: 15 lines
// Note that an alternative proof is to remove this invariant altogether, as Safety is
// also implied by OwnershipInv
lemma InvNextServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerOwnsLockImpliesNoClientsOwnsLock(c, v')
{
  forall i | v'.ValidHistoryIdx(i) && ServerHost.HostOwnsUniqueKey(c.server[0], v'.History(i).server[0], 0)
  ensures forall id: int | c.ValidClientIdx(id) :: !ClientHost.HostOwnsUniqueKey(c.clients[id], v'.History(i).clients[id], 0)
  {
    VariableNextProperties(c, v, v');
    OwnershipInvInductive(c, v, v');
    if i == |v'.history| - 1 {
      assert !NoServerHostOwnsKey(c, v', 0);  // trigger
    }
  }
}
```

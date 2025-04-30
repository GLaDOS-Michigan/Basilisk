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
// modified: 7 lines
// Note that the proof is also complete by deleting this lemma
lemma InvNextSafety(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Safety(c, v')
{
  OwnershipInvInductive(c, v, v');
}
```

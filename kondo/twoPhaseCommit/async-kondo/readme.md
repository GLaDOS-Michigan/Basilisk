# Notes

Generates async proof from sync proof.

## Commands

Generate monotonicity and message invariants:

```bash
./local-dafny/Scripts/dafny /msgInvs distributedSystem.dfy
```

Generate async draft proof:

```bash
./local-dafny/Scripts/dafny /genAsyncProof ../centralized/applicationProof.dfy
```

To complete the draft proof, the user must fill in the body for lemma `InvNextAC3`, given below.

```dafny
// modified: 19 lines
lemma InvNextAC3(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AC3Contrapos(c, v')
{
  AC3ContraposLemma(c, v);
  VariableNextProperties(c, v, v');
  if ! AllPreferYes(c) && CoordinatorHasDecided(c, v'.Last()) {
    var noVoter: HostId :| c.ValidParticipantId(noVoter) && c.participants[noVoter].preference == No;
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if dsStep.CoordinatorHostStep? {
        /* Proof by contradiction. Suppose coordinator decided Commit. Then it must have
        a Yes vote from all participants, including noVoter. This is a contradiction */
        var l, l' := v.Last().GetCoordinator(c), v'.Last().GetCoordinator(c);
        if l.decision.WONone? && l'.decision == WOSome(Commit) {
          YesVotesContainsAllParticipantsWhenFull(c, v);
          assert noVoter in v.Last().GetCoordinator(c).yesVotes;
        }
    }
  }
}
```


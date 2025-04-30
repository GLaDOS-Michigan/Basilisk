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

In this case, the generated draft is the final proof.

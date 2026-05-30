# Limitation Ledger: BEDC Rule 110 Finite Witness Artifacts

This ledger records the limits that must appear in any promoted manuscript.
The source snapshot is `D:/omega/newmath` `origin/dev`
`3fb3d6a0641767388a401883062aa522ea0b397b`.

## Claim Boundaries

| Claim surface | Permitted claim | Forbidden claim |
|---|---|---|
| Finite BEDC witnesses | Finite witness assertions are represented as manifests and checked by artifact commands | Finite witnesses imply universal theorem closure |
| Cyclic-tag route | Manifest assertions can be lowered to cyclic-tag surfaces and tested | Cyclic-tag execution replaces Lean proof checking |
| Rule 110 direct-carrier route | Generated `.r110.ct` manifests exercise direct-carrier assertions in the reported surface | Rule 110 proves all Lean declarations or all CIC statements |
| Cook packet surface | Cook symbolic and semantic round-trip checks cover the reported `.algo.r110.ct` manifests | The artifact proves a complete phase-exact Cook universality construction unless separately verified |
| Martinez data surface | Phase verifier and collision rows are checked against reported data | Collision-audit failures can be ignored without discussion |

## Reported Limitation from `STATUS.md`

`make test-collision-audit` reports:

```text
table audit (cook_collisions.c full 33 rows): 26/33 PASS, 7 FAIL
Martinez 2012 Table 1/Table 2 cross-check: 33 rows, 33 matched,
0 only-in-paper, 0 only-in-table
```

The promoted paper must decide whether this is:

1. a blocker that must be fixed before submission; or
2. a scoped diagnostic that is reported as a limitation outside the finite
   witness core.

It cannot be omitted.

## Required Abstract Language

Any promoted abstract must include the phrase "finite witness" or an equivalent
explicit finite-scope phrase.  It must avoid phrases suggesting universal proof
closure, replacement of Lean, or unrestricted Rule 110 proofhood.

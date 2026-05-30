# Scope Contract: BEDC Rule 110 Finite Witness Artifacts

## Paper Unit

This seed is an intake-stage candidate for an artifact paper on finite BEDC
witness manifests lowered through cyclic-tag and Rule 110 execution surfaces.
The paper unit is the artifact, trust chain, manifest inventory, executable
checks, and limitation ledger.

## Central Claim

The central claim is that a finite set of BEDC witness assertions can be
represented as manifest artifacts and checked through a low-trust executable
route involving cyclic-tag systems and Rule 110 direct-carrier manifests.  The
claim is finite and artifact-bounded.

## In-Scope Artifact Surfaces

| Surface | Pinned source path | Paper role |
|---|---|---|
| Artifact overview | `rule110/README.md` | Trust-chain and reproducibility summary |
| Citable status | `rule110/STATUS.md` | Counts, coverage, commands, limitations |
| Evaluators | `rule110/evaluator/` | Low-trust cyclic-tag and Rule 110 execution substrate |
| Encoders | `rule110/encoder/` | GroundCompiler and Cook/Rule110 lowering surface |
| Manifests | `rule110/manifests/` | Source and generated witness assertions |
| Tests | `rule110/tests/` | Test binaries and audit checks |
| Docs | `rule110/docs/` | Manifest format, theorem encoding, Cook data |
| Lean source boundary | `lean4/BEDC/FKernel/`, `lean4/BEDC/GroundCompiler/` | Source families mirrored by manifests |

## Non-Claims

- The paper must not claim Rule 110 proves universal CIC statements.
- The paper must not claim the artifact replaces Lean's kernel.
- The paper must not claim finite witness coverage is universal theorem
  closure.
- The paper must not claim a complete phase-exact Cook construction beyond the
  verified artifact scope.
- The paper must not hide the collision-audit limitation recorded in
  `rule110/STATUS.md`.

## Promotion Evidence Required

Promotion requires:

1. Rechecked artifact counts at the chosen source commit.
2. A trust-chain table with line counts and commands.
3. A limitation ledger separating finite witness, cyclic-tag witness, Rule 110
   direct-carrier witness, and Cook/Martinez diagnostic surfaces.
4. A reproducibility note for `make clean && make && make test`.
5. A decision on whether `make test-collision-audit` is a blocking gate or a
   scoped diagnostic.

## First Route

This seed is suitable for a CICM presentation/artifact route if the artifact
counts and limitations are rechecked.  It should not be merged into the
automation-pipeline paper except as one possible case study.

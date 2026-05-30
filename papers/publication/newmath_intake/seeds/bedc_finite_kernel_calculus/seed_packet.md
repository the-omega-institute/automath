# Seed Packet: BEDC Finite Kernel Calculus

## Proposed Paper Unit

A formal logic paper isolating the finite BEDC kernel: marks, histories,
relations, extensions, continuations, asks, bundles, signatures, packages,
gap ledgers, and naming certificates.

## Priority

P0.

## Source of Truth

- Repo: `D:/omega/newmath`
- Ref: `origin/dev`
- Commit: `3fb3d6a0641767388a401883062aa522ea0b397b`

## Candidate Claim

The paper claims that a small finite-kernel calculus can derive naming and
certificate surfaces from primitive mark/history constructors and relation
discipline, without importing ordinary mathematical primitives as initial
objects.

## Non-Claims

- It is not a BEDC grand-theory paper.
- It does not claim to replace set theory, type theory, or category theory.
- It does not claim all downstream concrete instances are mature.
- It does not rely on Rule 110 or AI automation for the logical result.

## Key Source Paths

- `lean4/BEDC/FKernel/`
- `lean4/BEDC/GroundCompiler/`
- `papers/bedc/parts/finite_kernel_theory/`
- `papers/bedc/parts/proof_obligations/`
- `papers/bedc/parts/concrete_instances/`
- `docs/dossier/distinction-as-foundation.qmd`
- `docs/dossier/boundary-not-axiom.qmd`
- `docs/dossier/zero-information-debt.qmd`

## Evidence to Extract

- Exact syntax and constructors.
- Equivalence and no-confusion theorems for mark/history sameness.
- Extension and continuation determinism/closure theorems.
- Signature and package coverage/separation.
- NameCert theorem inventory.
- A short non-claim registry explaining which ordinary mathematical objects
  are outside the finite kernel and only appear as derived interfaces.

## Intake Artifacts Added

- `scope_contract.md`: exact paper unit, non-claims, and route boundary.
- `declaration_inventory_seed.md`: first exact Lean declaration seed from the
  pinned `origin/dev` source snapshot.
- `promotion_checklist.md`: remaining tasks before active paper promotion.

## Current Route

This seed should remain intake-only until a smaller theorem spine is curated
from `declaration_inventory_seed.md`.  It is stronger as a logic/formal-calculus
paper than as a fast short-window submission.  Do not merge it with the
automation-pipeline or Rule110 artifact papers.

## Promotion Target

Candidate active directory:

`papers/publication/2026_bedc_finite_kernel_calculus/`

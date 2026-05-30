# GroundCompiler Placement Decision: BEDC Finite Kernel Calculus

This is an intake-level placement decision.  It does not promote the seed and
must not be treated as a manuscript section or `THEOREM_LIST.md`.

- decision date: 2026-05-31
- seed:
  `papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`
- pinned source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Decision

GroundCompiler material should be appendix/interface-only for this paper route.
It should not be a main section and should not be part of the main finite-kernel
theorem spine.

## Reason

The selected finite-kernel spine is about primitive marks, histories,
extension, continuation, bundles, and ask policies.  Those surfaces are the
kernel-level calculus.  GroundCompiler files are useful boundary evidence for
encoding and rejection interfaces, but they are downstream implementation
surfaces rather than primitive kernel constructors.

Keeping GroundCompiler out of the main spine reduces three risks:

- overclaiming executable encodings as mathematical theoremhood;
- mixing artifact-engineering obligations with the finite-kernel calculus;
- weakening the need for one explicit upstream packaging theorem such as
  `finite_kernel_interface_soundness`.

## Allowed Use

A promoted manuscript may use GroundCompiler material only to support an
interface-boundary paragraph or appendix table.  Acceptable uses are:

- naming encoding surfaces as downstream consumers of the finite kernel;
- listing reject taxonomies as engineering obligations;
- explaining why implementation channels are not primitive kernel objects;
- pointing to future artifact work without claiming Rule110 validation.

## Not Allowed

A promoted manuscript must not use GroundCompiler material to claim:

- completeness of the finite kernel;
- semantic soundness of downstream artifacts;
- executable encodings as proof evidence;
- replacement of the missing packaging theorem;
- Rule110 or artifact-level validation for this paper route.

## Consequence For Next Work

The next source-side work item remains the packaging theorem described in
`upstream_packaging_work_order.md`.  If source-side work is approved, agents
should add or identify a theorem in the finite-kernel source area, not in
GroundCompiler.

After that work, update this seed with a source update note before any
journal-style promotion discussion.

## Guardrail

This note is not authorization to create:

- `papers/publication/2026_*`;
- `main.tex` in this seed;
- `PIPELINE.md` in this seed.


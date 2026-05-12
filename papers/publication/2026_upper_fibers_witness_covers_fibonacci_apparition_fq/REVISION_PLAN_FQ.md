# FQ Deep-Revision Plan

This active fork is not in a manual submission queue. It is a deep-revision
candidate for The Fibonacci Quarterly, created from the parked RJ archive after
the May 2026 rejection.

## Gate Status

- Submitted/source-history archive:
  `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj`.
- Duplicate submitted/archive folder:
  `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint`.
- Active revision folder:
  `2026_upper_fibers_witness_covers_fibonacci_apparition_fq`.
- Submission rule: do not submit this fork until the arithmetic revision,
  reproducibility synchronization, overlap gate, and final human review all
  pass.

## Mandatory Fixes Before FQ

1. Keep the corrected `n=30` narrative: the five displayed minimal generators
   realize only the verified types in the data, not all eight admissible
   three-coordinate types.
2. Audit `thm:three-coordinate-nonemptiness` as an actual if-and-only-if
   selection criterion, separating abstract admissibility from Fibonacci
   realization.
3. Close the witness-cover proof with explicit checks of atomicity,
   pairwise coprimeness, lcm coverage, and irredundance via `E_n`.
4. Close the connected-block proof, especially `alpha(q_C)=n_C` and
   minimality descent to connected components.
5. Add at least one genuine arithmetic increment beyond the RJ version. Current
   acceptable candidates are a sharp three-coordinate nonemptiness theorem, a
   theorem-level computational pattern with expanded verified data, or a
   nontrivial estimate for `A(n)` or `#M_n`.
6. Synchronize `main.tex`, examples `n=20` and `n=30`, generated table output,
   abstract, introduction, and the reproducibility paragraph.
7. Draft a new FQ cover letter only after the manuscript revision is complete.

## Current Editorial Decision

The correct action is revision, not immediate resubmission. If no new arithmetic
increment can be proved, park the fork and wait for a stronger result rather
than sending a cosmetic FQ version.

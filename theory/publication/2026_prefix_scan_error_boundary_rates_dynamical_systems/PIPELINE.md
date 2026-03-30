# TRACK_BOARD

- Paper: `2026_prefix_scan_error_boundary_rates_dynamical_systems`
- Target journal: `Ergodic Theory and Dynamical Systems (ETDS)` (provisional)
- Current status: `pilot onboarding`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `in progress`
- P2 Research Extension: `pending`
- P3 Journal-Fit Rewrite: `pending`
- P4 Editorial Review: `pending`
- P5 Full Improvement: `pending`
- P6 Lean / Formalization Sync: `pending`
- P7 Submission Pack: `pending`

## Active Claims

- `unassigned / P1 / README + SOURCE_MAP + THEOREM_LIST + BIB_SCOPE / onboarding complete`

## Blocking Issues

- no recent target-journal reconnaissance yet
- no Lean linkage notes yet
- bibliography still inherited from the master paper

## Next Parallel Batch

- traceability agent: attach source line anchors and Lean labels
- bibliography/recon agent: survey recent ETDS papers
- research agent: decide whether the theorem chain is already sharp enough or needs one stronger result

---

# SOURCE_MAP

## Primary source

- `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/spg/sec__spg.tex`

## Extraction boundary

This paper is a strict extraction of the scan-error / clarity part of the SPG
source.  It keeps the measurable decision-error chain and leaves out the
broader address-semantics, capacity, and protocol packages.

## Core label map

- `def:spg-scan-error-profile`
- `prop:spg-scan-error-cylinder`
- `prop:spg-clarity-bayes-optimality`
- `cor:spg-clarity-basic`
- `thm:spg-scan-tanaka-stokes`
- `def:spg-boundary-cylinder-dimension`
- `thm:spg-clarity-boundary-dimension`
- `thm:spg-clarity-volume-boundary-scaling`

## Deliberate exclusions

- recursive-addressing statements now absorbed by the ETDS-facing `E2` paper;
- capacity and collision statements;
- any logic-expansion or forcing language;
- later arithmetic, POM, or zeta consequences.

---

# THEOREM_LIST

## Main statements retained in this draft

- `def:spg-scan-error-profile`
  Defines the optimal observable classification error on the prefix
  sigma-algebra `\mathcal F_m`.

- `prop:spg-scan-error-cylinder`
  Gives the exact cylinder decomposition of the scan-error profile.

- `prop:spg-clarity-bayes-optimality`
  Identifies the Bayes-optimal threshold rule on each prefix atom.

- `cor:spg-clarity-basic`
  Records the basic monotonicity and limiting properties of the profile.

- `thm:spg-scan-tanaka-stokes`
  Rewrites error decay as a discrete Tanaka--Stokes type accumulation law.

- `def:spg-boundary-cylinder-dimension`
  Defines the boundary-cylinder counting scale and associated dimension proxy.

- `thm:spg-clarity-boundary-dimension`
  Gives the upper convergence law from boundary-cylinder growth.

- `thm:spg-clarity-volume-boundary-scaling`
  Gives the two-sided scaling law under boundary thickness.

## Supporting examples retained

- `ex:finite-horizon-event`
- `ex:golden-mean-specialization`

## Next traceability step

For each retained statement, attach the exact source line range in the SPG
master section and add Lean label/declaration anchors where available.

---


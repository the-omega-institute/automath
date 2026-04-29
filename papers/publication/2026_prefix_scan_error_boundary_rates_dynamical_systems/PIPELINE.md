# Pipeline: Prefix Scan Error / Boundary Rates (ETDS)
Target: Ergodic Theory and Dynamical Systems (ETDS) (provisional)
Status: pilot onboarding (P1 in progress)

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | ETDS provisional target |
| P1 Traceability | in progress | -- | SOURCE_MAP and THEOREM_LIST produced; source line anchors and Lean labels pending |
| P2 Research Extension | pending | -- | Decide whether theorem chain needs strengthening |
| P3 Journal-Fit Rewrite | pending | -- | |
| P4 Editorial Review | pending | -- | |
| P5 Integration | pending | -- | |
| P6 Lean Sync | pending | -- | No Lean linkage notes yet |
| P7 Submission Pack | pending | -- | |

### Blocking Issues

- No recent target-journal reconnaissance
- No Lean linkage notes
- Bibliography still inherited from master paper
- Source line anchors and Lean label attachments pending

## Theorem Inventory

### Core claims (8)

- `def:spg-scan-error-profile`: Optimal observable classification error on prefix sigma-algebra
- `prop:spg-scan-error-cylinder`: Exact cylinder decomposition of scan-error profile
- `prop:spg-clarity-bayes-optimality`: Bayes-optimal threshold rule on each prefix atom
- `cor:spg-clarity-basic`: Basic monotonicity and limiting properties of the profile
- `thm:spg-scan-tanaka-stokes`: Error decay as discrete Tanaka-Stokes accumulation law
- `def:spg-boundary-cylinder-dimension`: Boundary-cylinder counting scale and dimension proxy
- `thm:spg-clarity-boundary-dimension`: Upper convergence law from boundary-cylinder growth
- `thm:spg-clarity-volume-boundary-scaling`: Two-sided scaling law under boundary thickness

### Supporting examples

- `ex:finite-horizon-event`
- `ex:golden-mean-specialization`

## Source Map

**Primary source:** `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/spg/sec__spg.tex`

**Extraction boundary:** Strict extraction of the scan-error / clarity part of the SPG source. Keeps the measurable decision-error chain; leaves out address-semantics, capacity, and protocol packages.

**Deliberate exclusions:**
- Recursive-addressing statements (absorbed by the ETDS-facing sigma-nonexpansion paper)
- Capacity and collision statements
- Logic-expansion or forcing language
- Arithmetic, POM, or zeta consequences

## Stage Notes

### P1 Traceability

Core label map produced with 8 claims. Next traceability step: attach exact source line ranges in SPG master section and add Lean label/declaration anchors where available.

### Pending next steps

- Traceability agent: attach source line anchors and Lean labels
- Bibliography/recon agent: survey recent ETDS papers
- Research agent: decide whether theorem chain is already sharp enough or needs a stronger result

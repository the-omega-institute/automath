# LEAN_SYNC_NOTE 2026-03-30

Paper: `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
Target: Ergodic Theory and Dynamical Systems (ETDS)

## Coverage summary

- Total theorem-level claims: 17 (14 retained + 3 open-system)
- VERIFIED: 0
- PARTIAL: 4
- MISSING: 11
- N/A: 2

### PARTIAL (4)

| Label | Paper statement | Lean status | Diff notes |
|---|---|---|---|
| `prop:scan-error-cylinder` | scan error profile on prefix cylinders | SPG module has `scanError` definition (`def:spg-discrete-scan-error` in ScanErrorDiscrete.lean), cylinder sets (`cylinderWord` in Cylinder.lean), and prefix scan error (`prefixScanError` / `prefixScanErrorMeasure`). Basic properties proved: zero on observable events, Bayes half-bound, boundary decomposition. However, the paper's full cylinder-based error profile with recursive addressing is not formalized. | Lean covers the scan-error definition and basic properties but not the recursive-addressing specialization claimed in the paper |
| `prop:bayes-optimality` | Bayes optimality bound | SPG module has `scanError_le_half` (Bayes half-bound `2*epsilon <= 1` in discrete and measure versions). The paper claims a sharper Bayes-optimality statement. | Lean proves the half-bound; the full optimality characterization is missing |
| `thm:inverse-limit-determinacy` | inverse-limit determinacy for address chains | Lean has `inverseLimitEquiv` (bijection between `CompatibleFamily` and `XInfinity` in InverseLimit.lean), `prefixWord_surjective`, `prefixWord_stableValue_coherent`. The paper's determinacy theorem for address chains is a broader dynamical statement. | Lean covers the inverse-limit structure but not the full determinacy claim for address-chain dynamics |
| `thm:entropy-ledger` | entropy ledger | Lean has topological entropy = log phi (`topological_entropy_eq_log_phi` in Entropy.lean), entropy gap, and various moment-sum inequalities. The paper's entropy-ledger theorem is a more specific statement about survivor Renyi pressure and collision counting. | Lean covers topological entropy but not the specific Renyi/survivor entropy ledger formulation |

### MISSING (11)

| Label | Description | Notes |
|---|---|---|
| `cor:sigma-nonexpansion` | recursive addressing does not enlarge visible sigma-algebra | No Lean counterpart; sigma-algebra non-expansion is not formalized |
| `thm:finite-depth-collapse` | finite-depth collapse criterion | No Lean counterpart |
| `thm:complete-address-reconstruction` | reconstruction from complete address data | No Lean counterpart |
| `thm:tanaka-stokes` | discrete Tanaka-Stokes identity | Noted as future work item 14 in IMPLEMENTATION_PLAN.md ("prove discrete Tanaka formula"); not yet implemented |
| `thm:clarity-boundary-dimension` | boundary dimension for clarity | No Lean counterpart |
| `thm:weighted-boundary-transfer` | weighted boundary transfer | No Lean counterpart |
| `cor:pressure-gap` | pressure gap corollary | Lean has entropy gap (log 2 - log phi > 0) but not the thermodynamic pressure-gap formulation |
| `thm:double-budget-poisson` | double-budget Poisson threshold | No Lean counterpart |
| `thm:register-lower-bound` | register lower bound | No Lean counterpart for the ETDS-specific formulation; Conclusion chapter has `godelLift_feasibility` and `readout_binary_steps_window6` but these are POM-specific, not the ETDS register bound |
| `thm:first-entry-escape-rate` | first-entry escape rate | No Lean counterpart |
| `thm:quasistationary-ambiguity` | quasistationary ambiguity | No Lean counterpart |

### N/A (2)

| Label | Reason |
|---|---|
| `cor:survivor-pressure-recovery` | open-system lane; scope decision still pending per SOURCE_MAP.md |
| observer-spacetime propositions | listed in THEOREM_LIST.md as "may need relocation" -- these are in `sec_observer_spacetime.tex` of the APAL paper, not this paper |

### Coverage rate: 0 VERIFIED + 4 PARTIAL out of 15 active claims = 0% verified, 27% partial

## Recommended formalization backlog

Priority-ordered list of MISSING theorems worth formalizing, considering existing Lean infrastructure:

1. `cor:sigma-nonexpansion` -- the paper's signature result; would need measurable-space infrastructure on the inverse-limit tower (Lean already has `XInfinity`, `CompatibleFamily`, `restrict`)
2. `thm:tanaka-stokes` -- already identified as future work item 14 in IMPLEMENTATION_PLAN.md; discrete Stokes/defect infrastructure exists in `Defect.lean`
3. `thm:finite-depth-collapse` -- could build on existing `inverseLimitEquiv` and the modular tower
4. `cor:pressure-gap` -- Lean already has entropy = log phi and entropy gap > 0; bridging to thermodynamic pressure is incremental
5. `thm:complete-address-reconstruction` -- reconstruction theorem; may follow from inverse-limit + Zeckendorf uniqueness
6. `thm:clarity-boundary-dimension` -- would need Hausdorff/box-counting dimension infrastructure
7. `thm:weighted-boundary-transfer` -- would need boundary-layer + transfer-operator infrastructure
8. `thm:double-budget-poisson` -- requires probability/Poisson infrastructure
9. `thm:register-lower-bound` -- pigeonhole/counting; closest to existing style
10. `thm:first-entry-escape-rate` -- requires open-system dynamics
11. `thm:quasistationary-ambiguity` -- requires quasistationary measure theory

## Mismatches

1. **Entropy formulation**: Lean proves `topological_entropy_eq_log_phi` (the golden-mean shift has topological entropy log phi). The paper's `thm:entropy-ledger` is about a survivor Renyi pressure ledger, which is a distinct (though related) statement. Care needed to avoid citing the Lean result as covering the paper claim.

2. **Scan error scope**: Lean's SPG module covers scan error in a general discrete/measure setting with Bayes half-bound. The paper specializes to recursive-addressing cylinder refinements. The Lean results are prerequisites but do not cover the recursive-addressing specialization.

3. **Inverse-limit scope**: Lean's `InverseLimit.lean` provides the set-theoretic inverse-limit bijection. The paper's `thm:inverse-limit-determinacy` makes a dynamical determinacy claim that goes beyond the set-theoretic bijection.

## Source coverage gap

IMPLEMENTATION_PLAN.md future work items 13-18 (Phase C: SPG measure extension) directly target infrastructure needed by this paper (conditional expectation, Tanaka-Stokes, martingale, Shannon, Bayes generalization, Lipschitz). None of these are completed.

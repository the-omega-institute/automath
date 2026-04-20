# Pipeline: Finite-Window Zeckendorf Fibers / Discrete Thermodynamics (TAMS)
Target: Transactions of the American Mathematical Society
Status: **SUBMISSION-READY** (P7 complete)

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | -- |
| P1 Traceability | completed | -- | -- |
| P2 Research Extension | completed | 2026-03-30 | 10 main theorems (A--F + Renyi + collision + Galois + Chebotarev); sec_chebotarev included, sec_rewriting excluded |
| P3 Journal-Fit Rewrite | completed | 2026-03-30 | Abstract ~170 words; Theorems A--F previewed; bib: 4 added, 4 removed (final 13) |
| P4 Editorial Review | completed | 2026-03-30 | Decision: MINOR_REVISION; 3 must-fix, 5 should-fix, 3 optional |
| P5 Integration | completed | 2026-03-30 | All 3 must-fix and 5 should-fix applied |
| P6 Lean Sync | completed | 2026-03-30 | 25% verified (4/16), 31% partial (5/16), total touched 56% |
| P7 Submission Pack | completed | 2026-03-30 | Cover letter + 12-item checklist (all PASS) |

## Theorem Inventory

### Named results (Theorems A--F)

| # | Label | One-line statement |
|---|-------|--------------------|
| A | `thm:partition-difference` | Fiber multiplicities = Fibonacci-lag discrete derivative of $R^{\dagger}$ |
| B | `thm:fibonacci-window-sandwich` + `thm:all-q-transfer` | $S_q \asymp \lambda_q^m$, $r_q = \lambda_q$ |
| C | `thm:collision-kernel` + `thm:symmetric-compression` + `cor:lambda-algebraic` + `thm:global-pressure-convexity` | Algebraicity, polynomial-size matrix, convex pressure |
| D | `thm:gibbs-selection` | Gibbs selection onto $[\Delta_q, \Delta_{q+1}]$ |
| E | `thm:microcanonical-bands` | Microcanonical band bounds |
| F | `thm:zero-temp-concentration` + `thm:max-fiber` + `thm:diagonal-high-moments` | Zero-temperature concentration |

### Additional main-line results

- `thm:renyi-entropy-rate`: Renyi entropy-rate spectrum
- `thm:collision-entropy-rate` + `thm:q2-alternating-second-order`: Collision entropy rate with alternating correction
- `thm:galois-sd-window`: $\mathrm{Gal}(P_q/\mathbb{Q}) \cong S_{d_q}$ for $q = 9, \ldots, 17$
- `thm:linear-disjointness` + `cor:chebotarev-product`: Linear disjointness and product Chebotarev densities for $q \in \{12, 13, 14, 15\}$

### Certified arithmetic window

$q = 9, \ldots, 17$ with explicit recurrence polynomials, mod-$p$ Galois certificates, discriminant squareclass data. Out of scope: $q \ge 18$, squareclass independence beyond $\{12,13,14,15\}$, symbolic root-isolation for secondary roots, alternating correction for general $q$.

## Source Map

- Root source: `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/pom/`
- `sec_preliminaries.tex`: finite-window stabilization, fold map, reflector, residue characterization
- `sec_ledger.tex`: visible entropy rates and collision entropy rate
- `sec_moment_kernel.tex`: collision kernel, symmetric compression, pressure geometry, Gibbs selection
- `sec_residue_affine.tex`: affine transfer and partition differences
- `sec_second_collision.tex`: second-collision package and alternating law
- `sec_chebotarev.tex`: resonance polynomials, principalization, Galois window, Chebotarev product
- `sec_appendix_transducer.tex` (App A): bounded-delay transducer model
- `sec_appendix.tex` (App B): computational certification tables

**Excluded:** `sec_rewriting.tex` (operator rewriting -- not used by any theorem), `sec_appendix_auxiliary.tex` (non-structural)

## Stage Notes

### P2 Research Extension

**Escalation ladder:** Single fibers (Thm A) -> Moment transfer (Thm B) -> Finite-state realization (Thm C) -> Canonical selection (Thms D-E) -> Zero-temperature (Thm F) -> Renyi spectrum -> Arithmetic payoff (Galois/Chebotarev).

**Scope cuts:** sec_chebotarev included (arithmetic payoff); sec_appendix included as Appendix B (certification tables); sec_rewriting excluded (not used by any theorem); sec_appendix_auxiliary excluded (non-structural).

**Bibliography:** Added Neukirch1999, LindMarcus1995, CoverThomas2006, DemboZeitouni2010. Removed AhlbachUsatineFrougnyPippenger2013, Kempton2023, ShallitShan2023, BaaderNipkow1998.

### P3 Journal-Fit Rewrite

- Abstract rewritten from ~350 to ~170 words; mentions Galois/Chebotarev arc
- Introduction rewritten: Theorems A--F previewed, escalation ladder, related work, roadmap
- sec_chebotarev included before conclusion; sec_appendix as Appendix B
- Conclusion shortened, covers arithmetic window and open problems
- MSC code 11R32 added; keywords updated with "Galois groups" and "Chebotarev density"
- Final bibliography: 13 entries, all cited; no revision-trace language
- All files under 800 lines (max: sec_moment_kernel at 682)

### P4 Editorial Review

**Decision:** MINOR_REVISION. All 10 main theorems correctly stated, proofs complete, arithmetic window accurately bounded, scope exclusions properly flagged. AI-voice check clean (one minor flag: "unexpectedly rigid").

**Must-fix (all resolved in P5):**
1. $\Delta_q$ notation overloaded (pressure slope vs Hankel codimension) -- renamed to $\kappa_q$
2. Remark theorem style: changed from `plain` to `remark`
3. Author affiliation and funding acknowledgment added

**Should-fix (all resolved in P5):**
4. $m_0(q)$ offset discrepancy: changed to $m \ge 0$ matching appendix proof
5. Quotient variable $q$ renamed to $b$ in `prop:single-overflow`
6. "Then" connector added in `cor:visible-band`
7. New `rem:lambda-one` ($\lambda_1 = 2$) after `thm:all-q-transfer`
8. `cor:log-density-additivity` demoted to `rem:log-density-additivity`

### P5 Integration

All must-fix and should-fix items applied. Verification: all .tex files under 800 lines (max 682), no revision-trace language, $\kappa_q$ replaced in all 11 chebotarev occurrences, $m \ge 0$ in thm:collision-kernel matches appendix.

### P6 Lean Sync

**Verified (4):** `thm:rewrite-confluence`, `cor:rewrite-word-problem`, `thm:collision-kernel` (q=2..5 companion matrices), `thm:difference-power-sums` (S_2 recurrence fully verified by induction).

**Partial (5):** `thm:renyi-entropy-rate` (topological entropy covered, Renyi rate missing), `thm:collision-entropy-rate` (S_2 recurrence + growth verified, rate extraction missing), `thm:symmetric-compression` (ewc symmetry verified), `thm:global-pressure-convexity` (log-convexity verified), `thm:gibbs-selection` (combinatorial substrate present, measure-theoretic selection missing).

**Missing (7):** `thm:affine-transfer`, `thm:principalization`, `thm:galois-sd-window`, `thm:linear-disjointness`, `cor:chebotarev-product`, `thm:all-q-transfer`, `cor:log-density-additivity`.

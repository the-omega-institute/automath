# Pipeline: Scan Projection / Address Semantics / Sigma-Nonexpansion (ETDS)
Target: Ergodic Theory and Dynamical Systems (ETDS)
Status: submission-ready (author metadata missing)

## Stage Progress

| Stage | Status | Date | Notes |
|---|---|---|---|
| P0 Intake and Contract | completed | -- | -- |
| P1 Traceability | completed | -- | -- |
| P2 Research Extension | completed | 2026-03-30 | Single manuscript with strict hierarchy; open-system lane kept as principal application |
| P3 Journal-Fit Rewrite | completed | 2026-03-30 | Abstract compressed; introduction rewritten; section openers tightened |
| P4 Editorial Review | completed | 2026-03-30 | Decision: major revision; 3 blockers identified, all resolved in P5 |
| P5 Integration | completed | 2026-03-30 | 5 unused bib entries removed; sec_open_system split; intro subsection retitled |
| P6 Lean Sync | completed | 2026-03-30 | 0% verified, 27% partial (4/15 active claims have partial Lean support) |
| P7 Submission Pack | completed | 2026-03-30 | cover_letter_etds.txt + submission_checklist.md; 11 pass, 1 fail (author empty) |

### Remaining Blocker

`\author{}` in main.tex is empty. Author names, affiliations, and corresponding-author email must be inserted before submission.

## Theorem Inventory

### Structural results

- `cor:sigma-nonexpansion`: recursive addressing does not enlarge the visible sigma-algebra
- `thm:finite-depth-collapse`: finite-depth collapse criterion
- `thm:inverse-limit-determinacy`: inverse-limit determinacy for address chains
- `thm:complete-address-reconstruction`: reconstruction from complete address data

### Finite-observation and rate results

- `prop:scan-error-cylinder`, `prop:bayes-optimality`
- `thm:tanaka-stokes`: discrete Tanaka-Stokes identity
- `thm:clarity-boundary-dimension`, `thm:weighted-boundary-transfer`
- `cor:pressure-gap`

### Collision and information results

- `thm:double-budget-poisson`, `thm:entropy-ledger`, `thm:register-lower-bound`

### Open-system lane

- `thm:first-entry-escape-rate`, `cor:survivor-pressure-recovery`, `thm:quasistationary-ambiguity`

**Single-question formulation:** How much of the open symbolic dynamics of a hole is already visible in the Bayes error profile of finite observations of the binary coding?

## Source Map

- Root sources: `theory/.../sections/body/spg/` and `theory/.../sections/body/recursive_addressing/`
- `sec_preliminaries.tex`: symbolic factor setup and prefix cylinders
- `sec_recursive_addressing.tex`: recursive schemes, sigma-nonexpansion, finite-depth collapse, inverse-limit determinacy
- `sec_clarity.tex`: scan error profile, Bayes rule, Tanaka-Stokes identity, boundary transfer
- `sec_double_budget.tex`: survivor Renyi pressure, Poisson threshold, entropy ledger, register lower bound
- `sec_open_system.tex`: first-entry escape rate, quasistationary amplitudes
- `sec_open_system_resonance.tex`: error resolvents, cyclotomic resonance lifts, doubling-map example (split from sec_open_system at P5)
- `sec_spg.tex`: visible-word preliminaries and the Sturmian illustration

## Stage Notes

### P2 Research Extension

Scope decision: single ETDS manuscript with strict hierarchy. Central results: sigma-nonexpansion, inverse-limit determinacy, Tanaka-Stokes, weighted boundary transfer, first-entry escape rate, double-budget Poisson, entropy ledger. Sturmian illustration and open-system refinements remain subordinate.

### P3 Journal-Fit Rewrite

Abstract compressed from four paragraphs to single paragraph. Introduction rewritten: problem, setting, three main results stated upfront, context/comparison, explicit justification for open-system lane, organization. Section openers tightened. Conclusion mirrors tightened arc. Removed displayed equations from abstract and "two-component" merger language.

Remaining style issues deferred to referee feedback: title length, Sturmian placement, hidden-entropy subsection.

### P4 Editorial Review

Decision: major revision. Strengths: recognizable ETDS theorem package, open-system lane mathematically serious. Blockers: (1) too many coequal payoffs in front matter -- resolved by retitling intro subsection; (2) abstract slow to reach escape-rate point -- verified already compressed by P3; (3) open-system section reads as second thematic center -- shortened sec_double_budget title, tightened intro language.

### P5 Integration

- Removed 5 unused bibliography entries (MorseHedlund1940, PetersenErgodicTheory, KuipersNiederreiter1974, CoverThomas2006, Renyi1961Measures). Final: 17 entries, all cited.
- sec_open_system split into two files (433 + 517 lines) to meet 800-line limit
- Intro subsection retitled from defensive "Why the open-system lane belongs" to "Role of the open-system sections"
- All 14 theorem labels present; zero dangling refs; zero manifesto language

### P6 Lean Sync

**Partial (4):** `prop:scan-error-cylinder` (SPG module has scanError definition + basic properties), `prop:bayes-optimality` (Lean has half-bound), `thm:inverse-limit-determinacy` (Lean has inverseLimitEquiv), `thm:entropy-ledger` (Lean has topological_entropy_eq_log_phi).

**Missing (11):** sigma-nonexpansion, finite-depth collapse, complete address reconstruction, Tanaka-Stokes (noted as future work item 14), boundary dimension, weighted boundary transfer, pressure gap, double-budget Poisson, register lower bound, first-entry escape rate, quasistationary ambiguity.

Mismatches: Lean entropy is topological (h_top = log phi); paper's entropy-ledger is survivor Renyi formulation. Lean inverse-limit is set-theoretic; paper's determinacy is dynamical.

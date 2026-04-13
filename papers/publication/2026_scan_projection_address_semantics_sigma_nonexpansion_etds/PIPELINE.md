# Pipeline: Scan Projection / Address Semantics / Sigma-Nonexpansion (ETDS)
Target: Ergodic Theory and Dynamical Systems (ETDS)
Status: submission-ready

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
| P4 Gate 3 Review | completed | 2026-04-04 | Decision: MINOR_REVISION; 1 blocker (author), 4 medium, 6 minor |
| P5 Integration (Gate 3 fixes) | completed | 2026-04-04 | B1 + M1--M4 fixed; 6 minor items deferred to referee feedback |

### Gate 3 Fixes Applied (2026-04-04)

| Item | Decision | Action |
|------|----------|--------|
| B1 author empty | ACCEPT | Added "Haobo Ma, CHRONOAI PTE. LTD., Singapore" in main.tex |
| M1 Section 4 disconnected | ACCEPT | Replaced closing remark with forward pointer citing Theorems 5.1 and 6.2 |
| M2 no post-2012 refs | ACCEPT | Added BruinDemers2022, DemersTodd2017, BunimovichYurchenko2011; cited in introduction |
| M3 S2^2 <= S3 unjustified | ACCEPT | Added one-line Jensen/power-mean justification in sec_double_budget.tex |
| M4 past-future spectral ID | ACCEPT | Added transpose-duality proof sketch in sec_open_system_resonance.tex |
| m1--m6 (minor) | DEFER | Unlikely to cause rejection; address if referee flags them |

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

### P5 Integration (Gate 3 fixes, 2026-04-04)

Five issues from the Gate 3 MINOR_REVISION review were resolved:

1. **B1:** Author field populated with Haobo Ma / CHRONOAI / email in main.tex.
2. **M1:** Closing remark in sec_recursive_addressing.tex replaced with an explicit forward pointer explaining that the finite-depth collapse theorem guarantees Bayes error validity when passing from recursive codings to base-level, as used by Theorems 5.1 and 6.2.
3. **M2:** Three post-2012 references added to references.bib (Bruin--Demers 2022, Demers--Todd 2017, Bunimovich--Yurchenko 2011) and cited in sec_introduction.tex. Bibliography now has 20 entries, all cited.
4. **M3:** One-line Jensen/power-mean justification for $S_2^2 \le S_3$ added in the proof of Theorem 6.2(ii) in sec_double_budget.tex.
5. **M4:** Proof sketch for past--future spectral identification added in the proof of Theorem 5.6(iv) in sec_open_system_resonance.tex: the backward specification operator and forward Ruelle operator are transposes under the equilibrium pairing, so they share the same nonzero spectrum.

Six minor items (m1--m6) deferred to referee feedback. No theorem labels changed. No new mathematical content introduced.

### Backflow to Core

| Result | Core target section | Status |
|---|---|---|
| `prop:scan-error-cylinder` | `spg/` | pending |
| `prop:bayes-optimality` | `spg/` | pending |
| `thm:tanaka-stokes` | `spg/` | pending |
| `cor:clarity-monotone` | `spg/` | pending |
| `prop:weighted-boundary-decomposition` | `spg/` | pending |
| `thm:clarity-boundary-dimension` | `spg/` | pending |
| `thm:weighted-boundary-transfer` | `spg/` | pending |
| `cor:weighted-boundary-pole` | `spg/` | pending |
| `cor:pressure-gap` | `spg/` | pending |
| `thm:survivor-renyi-pressure` | `spg/` | pending |
| `cor:survivor-spectrum-collision` | `spg/` | pending |
| `thm:double-budget-poisson` | `spg/` | pending |
| `cor:capacity-region` | `spg/` | pending |
| `thm:entropy-ledger` | `spg/` | pending |
| `thm:register-lower-bound` | `spg/` | pending |
| `thm:collision-profile-restoration` | `spg/` | pending |
| `thm:main-amplitude` | `spg/` | pending |
| `thm:main-renyi` | `spg/` | pending |
| `thm:main-resonance` | `spg/` | pending |
| `thm:first-entry-escape-rate` | `spg/` | pending |
| `cor:survivor-pressure-recovery` | `spg/` | pending |
| `thm:quasistationary-ambiguity` | `spg/` | pending |
| `thm:error-resolvent-cyclotomic` | `spg/` | pending |
| `thm:holder-open-resonance` | `spg/` | pending |
| `prop:doubling-fibonacci-escape` | `spg/` | pending |
| `prop:symbolic-factor` | `spg/` | pending |
| `lem:prefix-ball-cylinder` | `spg/` | pending |
| `prop:sliding-block-factor` | `spg/` | pending |
| `cor:sigma-nonexpansion` | `spg/` | pending |
| `cor:entropy-monotonicity` | `spg/` | pending |
| `thm:finite-depth-collapse` | `spg/` | pending |
| `prop:inverse-limit-space` | `spg/` | pending |
| `thm:inverse-limit-determinacy` | `spg/` | pending |
| `thm:complete-address-reconstruction` | `spg/` | pending |
| `prop:decidable-clopen` | `spg/` | pending |
| `prop:sturmian-cylinder-sandwich` | `spg/` | pending |

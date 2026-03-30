# TRACK_BOARD

- Paper: `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
- Target journal: `Ergodic Theory and Dynamical Systems (ETDS)`
- Current status: `submission-ready`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed` -- artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
- P3 Journal-Fit Rewrite: `completed` -- artifact: `P3_REWRITE_NOTE_2026-03-30.md`
- P4 Editorial Review: `completed` -- artifact: `P4_EDITORIAL_REVIEW_2026-03-30.md`
- P5 Integration: `completed` -- triage and edits below
- P6 Lean / Formalization Sync: `completed` -- 0% verified, 27% partial (4/15 active claims have partial Lean support); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `completed` -- 2026-03-30; artifacts: `cover_letter_etds.txt`, `submission_checklist.md`

## P5 Triage Decision Log

### P2 recommendations

| # | Recommendation | Decision | Reason |
|---|---|---|---|
| 1 | Single manuscript with strict hierarchy | ACCEPT | Already implemented by P3 rewrite |
| 2 | Front matter: one finite-observation arc | ACCEPT | Already implemented by P3; verified in P5 |
| 3 | Sturmian/hidden-register subordinate | ACCEPT | Already implemented by P3 |

### P3 remaining style issues

| # | Recommendation | Decision | Reason |
|---|---|---|---|
| 1 | Shorten title | DEFER | Current title is descriptive and within ETDS norms; human-judgment call |
| 2 | Move Sturmian illustration to appendix | DEFER | Brief and mathematically clean; referee can request if needed |
| 3 | Cut hidden-entropy subsection | DEFER | Closes the collision loop; already subordinated in section opening |
| 4 | Remove 5 unused bibliography entries | ACCEPT | Removed: MorseHedlund1940, PetersenErgodicTheory, KuipersNiederreiter1974, CoverThomas2006, Renyi1961Measures |

### P4 strongest blockers

| # | Blocker | Decision | Action taken |
|---|---|---|---|
| 1 | Too many coequal payoffs in front matter | ACCEPT | Retitled intro subsection "Role of the open-system sections" (was defensive "Why the open-system lane belongs in this paper"); tightened text to position open-system results as direct consequences of the transfer theorem |
| 2 | Abstract too slow to reach escape-rate point | ACCEPT | P3 already compressed abstract to single paragraph; verified escape rate appears by line 5; no further change needed |
| 3 | Open-system section reads as second thematic center | ACCEPT | Shortened sec_double_budget title from "Survivor Renyi spectra, collision thresholds, and hidden information" to "Survivor Renyi spectra and collision thresholds"; tightened intro subsection language |

## P5 Edits Summary

### Bibliography

- Removed 5 unused entries: MorseHedlund1940, PetersenErgodicTheory, KuipersNiederreiter1974, CoverThomas2006, Renyi1961Measures
- Final bibliography: 17 entries, all cited
- No new citations added (BIB_SCOPE did not identify required additions beyond cleanup)
- Open-system lane literature already embedded in sec_open_system.tex opening paragraph

### Structural edits

- `sec_introduction.tex`: Renamed subsection "Why the open-system lane belongs in this paper" to "Role of the open-system sections"; rewrote text to remove defensive phrasing and position open-system results as direct consequences
- `sec_introduction.tex`: Adjusted Organization paragraph for sec_double_budget to match shortened title
- `sec_double_budget.tex`: Shortened section title from "Survivor Renyi spectra, collision thresholds, and hidden information" to "Survivor Renyi spectra and collision thresholds"
- `sec_open_system.tex`: Split into two files to meet the 800-line limit. `sec_open_system.tex` (433 lines) contains escape rates and quasistationary amplitudes. `sec_open_system_resonance.tex` (517 lines) contains error resolvents, cyclotomic lifts, and the doubling-map example. Added subsection headers for clearer internal navigation.
- `main.tex`: Added `\input{sec_open_system_resonance}` between `sec_open_system` and `sec_double_budget`

### Verification

- All 14 theorem labels from SOURCE_MAP.md present in manuscript
- Zero dangling \ref{} targets (all refs resolve to existing labels)
- Zero manifesto/AI language detected
- Section flow: preliminaries -> visible words -> structural background -> finite observation/transfer -> open system application -> collision/pressure -> conclusion
- Three main theorems stated in introduction with explicit bridges
- P4 acceptance condition met: front matter makes it impossible to read the paper as a bundle of adjacent manuscripts

## Active claims

- none

## Completed handoffs

- `orchestrator / P2 / P2_EXTENSION_NOTE_2026-03-30.md`
- `orchestrator / P4 / P4_EDITORIAL_REVIEW_2026-03-30.md`
- `rewrite agent / P3 / P3_REWRITE_NOTE_2026-03-30.md`
- `integration agent / P5 / TRACK_BOARD.md (this log)`
- `submission agent / P7 / cover_letter_etds.txt, submission_checklist.md, TRACK_BOARD.md`

## Blocking issues

- recent-paper recon not yet attached (non-blocking for submission)
- Lean formalization coverage remains low (0% verified, 27% partial) -- non-blocking for ETDS submission but noted for future work

## P7 Submission Pack

Date: 2026-03-30

### Artifacts produced

- `cover_letter_etds.txt` -- English cover letter addressed to the Editors of ETDS
- `submission_checklist.md` -- 12-item checklist; 11 pass, 1 fail (author field empty)

### Checklist summary

- Manuscript text complete: no TODO/FIXME markers
- Bibliography: 17 entries, all cited, no missing keys
- Abstract: ~141 words (ETDS limit ~200)
- Page estimate: ~35 pages
- No appendices, no figures, no tables
- MSC codes and keywords present
- All cross-references resolve (29 unique refs, 54 labels)
- No revision metadata in manuscript
- Lean formalization: 0% verified, 27% partial (documented in LEAN_SYNC_NOTE)

### Blocker requiring human action

- `\author{}` in main.tex is empty. Author names, affiliations, and corresponding-author email must be inserted before submission.

### Deferred editorial items (for referee feedback)

- Title length (currently 11 words + subtitle)
- Sturmian illustration placement (currently Section 3)
- Hidden-entropy subsection in Section 7

## Recommended next action

Insert author information into main.tex, compile final PDF, and submit to ETDS.

---

# THEOREM_LIST

## Structural results

- `cor:sigma-nonexpansion`
  recursive addressing does not enlarge the visible sigma-algebra
- `thm:finite-depth-collapse`
  finite-depth collapse criterion
- `thm:inverse-limit-determinacy`
  inverse-limit determinacy for address chains
- `thm:complete-address-reconstruction`
  reconstruction from complete address data

## Finite-observation and rate results

- `prop:scan-error-cylinder`
- `prop:bayes-optimality`
- `thm:tanaka-stokes`
- `thm:clarity-boundary-dimension`
- `thm:weighted-boundary-transfer`
- `cor:pressure-gap`

## Collision and information results

- `thm:double-budget-poisson`
- `thm:entropy-ledger`
- `thm:register-lower-bound`

## Open-system lane

- `thm:first-entry-escape-rate`
- `cor:survivor-pressure-recovery`
- `thm:quasistationary-ambiguity`

## Editorial objective

The final ETDS draft should present one theorem arc:
symbolic factor -> recursive addressability -> finite-observation error ->
pressure-gap / collision consequences.

---

# SOURCE_MAP

## Upstream source scope

- Root sources:
  `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/spg/`
  `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/recursive_addressing/`

## Local manuscript file map

- `sec_preliminaries.tex`
  symbolic factor setup and prefix cylinders
- `sec_recursive_addressing.tex`
  recursive schemes, sigma-nonexpansion, finite-depth collapse, inverse-limit determinacy
- `sec_clarity.tex`
  scan error profile, Bayes rule, Tanaka-Stokes identity, boundary transfer
- `sec_double_budget.tex`
  survivor Renyi pressure, Poisson threshold, entropy ledger, register lower bound
- `sec_open_system.tex`
  first-entry escape rate, quasistationary amplitudes
- `sec_open_system_resonance.tex`
  error resolvents, cyclotomic resonance lifts, doubling-map example
- `sec_spg.tex`
  visible-word preliminaries and the Sturmian illustration

## Retained theorem chain

- `cor:sigma-nonexpansion`
- `thm:finite-depth-collapse`
- `thm:inverse-limit-determinacy`
- `thm:complete-address-reconstruction`
- `prop:scan-error-cylinder`
- `prop:bayes-optimality`
- `thm:tanaka-stokes`
- `thm:clarity-boundary-dimension`
- `thm:weighted-boundary-transfer`
- `cor:pressure-gap`
- `thm:double-budget-poisson`
- `thm:entropy-ledger`
- `thm:register-lower-bound`
- `thm:first-entry-escape-rate`

## Scope decision still required

- determine whether `sec_open_system.tex` remains in the main line or becomes a sequel / appendix lane

---



# P2 Extension Note

Date: `2026-03-30`

## Scope decision

The paper should remain a single ETDS manuscript, but only with a strict
hierarchy:

1. visible symbolic factor and recursive addressability
2. finite-observation Bayes error and weighted boundary transfer
3. first-entry residue events as the principal open-system application
4. survivor Renyi pressure and collision threshold as the thermodynamic payoff

## Results that stay central

- `cor:sigma-nonexpansion`
- `thm:inverse-limit-determinacy`
- `thm:tanaka-stokes`
- `thm:weighted-boundary-transfer`
- `thm:first-entry-escape-rate`
- `thm:double-budget-poisson`
- `thm:entropy-ledger`

## Results that must remain subordinate

- the Sturmian illustration
- open-system refinements beyond the escape-rate theorem
- hidden-register restoration as a closing payoff rather than a competing main thread

## Single-question formulation

How much of the open symbolic dynamics of a hole is already visible in
the Bayes error profile of finite observations of the binary coding?

## Immediate rewrite consequence

The front matter should present the paper as one finite-observation
theorem arc with one main application lane, not as a merger of recursive
addressing, open systems, and information theory.

---



# P3 Rewrite Note

Date: `2026-03-30`
Stage: `P3 Journal-Fit Rewrite`

## What was restructured and why

### Abstract (main.tex)

The abstract was compressed from four long paragraphs (with two displayed equations) to a single paragraph stating one problem, one theorem package, and one payoff.  The old abstract enumerated too many coequal results (Tanaka identity, Markov boundary automaton, Renyi spectrum, hidden entropy) in a way that read as a catalog rather than a focused contribution.  The new abstract opens with a question ("what does the Bayes error detect about the open dynamics?"), answers it with three concrete claims (escape rate, quasistationary amplitude, cyclotomic resolvent), and closes with the thermodynamic consequence (survivor Renyi spectrum and Poisson birthday threshold).

### Introduction (sec_introduction.tex)

Completely rewritten.  The old introduction opened with general language about open dynamical systems and then described a "short structural component and a longer open-system component," which read as two separate papers merged.  The new introduction is organized as:

1. **Problem** -- one paragraph defining the Bayes error and stating the central question.
2. **Setting** -- one paragraph fixing the Markov/Gibbs setup.
3. **Main results** -- all three main theorems stated upfront with a one-sentence bridge between each.
4. **Context and comparison** -- literature positioning, unchanged in substance.
5. **Why the open-system lane belongs in this paper** -- explicit justification, as required by the task card.
6. **Organization** -- section-by-section guide.

This structure follows the ETDS profile: problem in dynamical-systems language from page one, principal theorem package stated early, secondary interpretation deferred.

### Section openings (sec_recursive_addressing, sec_clarity, sec_open_system, sec_double_budget)

Each section's opening paragraph was tightened to state its role relative to the main theorem arc rather than describing itself as a separate thematic center.  Specifically:

- `sec_recursive_addressing`: Reduced the opening to one sentence saying this is preparatory factor-theoretic background.  The closing remark was shortened to avoid restating the section's contents in list form.
- `sec_clarity`: Opening now names the tools (Bayes formula, Tanaka identity, boundary transfer) and forward-references Section 5 as the target application.
- `sec_open_system`: Opening now says "this section applies the weighted boundary transfer theorem to the principal setting of the paper" rather than "we now pass from general boundary transfer to the central open-system specialization."
- `sec_double_budget`: Opening now directly names the survivor Renyi pressure spectrum instead of framing it as "turning the open-system analysis into a pressure spectrum."

### Conclusion (sec_conclusion.tex)

Rewritten to mirror the tightened theorem arc.  Removed the paragraph about "a short structural section records that recursive visible refinements remain internal" -- that information is now in the section itself.  The two open questions are unchanged.

## What was cut and why

- **Displayed equations in the abstract**: The two displayed formulas for the Renyi partition function and its limit were removed.  They duplicated material from Theorem 1.2 and made the abstract too long for ETDS conventions.
- **"The paper has a short structural component and a longer open-system component"**: This sentence in the old introduction signaled a merged manuscript.  Replaced by the explicit "Why the open-system lane belongs" subsection.
- **"We will not use these statements as headline results below"**: The closing remark in sec_recursive_addressing was rewritten to avoid this self-deprecating formulation.
- **"supplementary information-theoretic statement"** phrasing in sec_double_budget: Replaced with a direct statement of what the subsection does.

## What was preserved exactly

- All theorem statements, proofs, definitions, and propositions are unchanged in mathematical content.
- All cross-references and label names are unchanged.
- The bibliography is unchanged.
- The section ordering is unchanged.
- Keywords and MSC codes are unchanged.

## Remaining style issues that need human judgment

1. **Title length**: The current title is 11 words with a subtitle.  An ETDS referee may prefer a shorter title.  A candidate: "Finite observation detects escape rates and cyclotomic resonances of open symbolic dynamics."  This is a human-judgment call.

2. **Sturmian section placement**: Section 3 (visible words and Sturmian illustration) is brief and somewhat peripheral.  A referee might ask whether the Sturmian material could be moved to an appendix or shortened further.  The mathematical content is clean, so the decision is editorial.

3. **Hidden-entropy subsection**: The final subsection of Section 7 (restoring collapsed Renyi spectra) is a supplementary information-theoretic result.  It is clearly subordinated now, but a referee might still ask whether it belongs in a dynamical-systems paper.  The case for keeping it: it closes the logical loop on the collision spectrum.  The case for cutting it: it is the most information-theoretic part of an otherwise dynamical paper.

4. **Bibliography width**: BIB_SCOPE notes that 5 of 22 entries are unused.  A bibliography cleanup pass should remove them, but this is a mechanical task best done after all content edits are final.

---



# P4 Editorial Review

Date: `2026-03-30`
Target venue: `Ergodic Theory and Dynamical Systems`
Decision: `major revision`

## Strengths

- The paper already contains a recognizable ETDS theorem package.
- The open-system lane is mathematically serious rather than decorative.
- The current review history suggests the draft is close to submit-ready structure.

## Strongest blockers

1. The manuscript still advertises too many coequal payoffs.
   Recursive addressing, weighted boundary transfer, escape rates, collision thresholds, and hidden entropy are all present, but the front matter does not yet impose a clear hierarchy.
2. The abstract and opening pages take too long to reach the pressure-gap and escape-rate point.
3. The role of the open-system section is not yet editorially disciplined enough.
   It still reads partly as a second thematic center rather than the principal application of the structural theory.

## Recommendation

- Keep `sec_open_system.tex` in the paper, but present it explicitly as the main application of the finite-observation framework.
- Keep `sec_double_budget.tex`, but subordinate hidden-register restoration to the survivor-pressure story.
- Make the introduction state one problem, one theorem chain, and one application lane.

## Acceptance condition

I would regard the draft as plausibly acceptable once the front matter,
scope hierarchy, and theorem roadmap make it impossible to read the paper
as a bundle of adjacent manuscripts.

---



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

---


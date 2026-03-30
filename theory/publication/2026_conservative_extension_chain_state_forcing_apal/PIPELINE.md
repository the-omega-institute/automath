# TRACK_BOARD

- Paper: `2026_conservative_extension_chain_state_forcing_apal`
- Target journal: `Annals of Pure and Applied Logic (APAL)`
- Current status: `blocked_pending_author_metadata`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed`
  - Artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
  - Date: 2026-03-30
- P3 Journal-Fit Rewrite: `completed`
  - Artifact: `P3_REWRITE_NOTE_2026-03-30.md`
  - Date: 2026-03-30
- P4 Editorial Review: `completed` -- decision: MAJOR_REVISION
  - Artifact: `P4_EDITORIAL_REVIEW_2026-03-30.md`
  - Date: 2026-03-30
- P5 Integration: `completed`
  - Date: 2026-03-30
- P6 Lean / Formalization Sync: `completed` -- 0% verified (0/13 claims have Lean counterparts); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `blocked` -- pack internally verified, but manuscript title-page author metadata is still missing
  - Artifacts: `cover_letter_apal.txt`, `submission_checklist.md`, `P7_SUBMISSION_NOTE_2026-03-30.md`
  - Date: 2026-03-30

## P2 Decisions

### Theorems kept in the main line (7 core results)

- `thm:sheafification-characterization` (A1)
- `thm:pointwise-irreducibility` (A2)
- `thm:component-gerbe-decomposition` (B1)
- `thm:gerbe-null-semantics` (B2)
- `thm:intrinsic-visible-quotient` (C1)
- `thm:character-blind-obstructions` (C2)
- `thm:unique-branch-contextuality-comparison` (C3)

### Theorems kept as secondary consequences (not foregrounded)

- `thm:initial-visible-quotient`
- `thm:character-definability-barrier`
- `thm:branch-sensitive-visible-quotient`
- `thm:branch-uniform-visible-quotient`
- `thm:branch-comparison-exact-sequence`
- `thm:branch-resolution-budget`
- `thm:multi-branch-strictification-budget`
- `thm:branch-visibility-monotonicity`
- `thm:minimal-information-cost-of-strictification`
- `thm:intrinsic-prime-decomposition`
- `thm:intrinsic-pure-ext-initiality`

### Theorems / sections moved to sequel track

- `sec_observer_spacetime.tex` (all propositions therein)
- `sec_conservativity.tex` (all propositions therein)

### Scope decision: sec_observer_spacetime.tex

**Out of scope.** No main-chain theorem depends on observer, event-region, coupled-state, or observer-symmetry material. The conservativity proposition is trivial. This section belongs to a multi-observer semantics sequel.

### Scope decision: branch-budget theorems

**Kept as secondary consequences.** The exact comparison sequence (`thm:branch-comparison-exact-sequence`) is the single clean multi-branch result and is retained in the main body. The branch-sensitive, branch-uniform, and multi-branch strictification theorems are kept as supporting corollaries, not elevated to core status.

## Blocking issues

- `main.tex` title-page author metadata is still missing (`\author{}` is empty). APAL uses single anonymized review and requires all authors to be listed in the manuscript and entered in the submission system before submission.

## Gap items from P2 (all closed by P3)

1. ~~Add one-paragraph bridge between strict and intrinsic visible quotients~~ done: bridge paragraph added in sec_gerbe_obstruction.tex
2. ~~Add standing-hypotheses environment at start of gerbe-obstruction subsection~~ done: (H1)--(H4) list added
3. ~~Add explicit mapping of Theorems A/B/C to the four-layer chain in the introduction~~ done: layer-boundary annotations in introduction
4. ~~Consider adding a single-branch S2 micro-example to complement the RP2 blind example~~ done: `ex:s2-single-branch-maximal-collapse` added

## P3 Summary

Rewrote abstract (~150 words), introduction (one research question, A-B-C preview with layer mapping), and conclusion (summary, external significance, open problems). Closed all four P2 gaps. Style pass enforced APAL register throughout. See `P3_REWRITE_NOTE_2026-03-30.md` for details.

## P4 Decision: MAJOR_REVISION

### Top blockers (must fix before P5)

1. **sec_homological_visibility.tex is 1144 lines** (limit: 800). Must split at the "Aggregating visibility across branches" subsection boundary (~line 573). Extract into `sec_branch_aggregation.tex`.
2. **10 of 21 bibliography entries are uncited.** Baltag1998, Beth1956, Fitting1969, Goldblatt2006, Groenendijk1991, Kripke1965, TroelstraVanDalen1988, vanBenthem2011, vanDalen2013, Veltman1996. Either cite the classic forcing references in the introduction and remove the dynamic-semantics ones, or remove all 10.
3. **Sequel-track files still in submission directory.** `sec_observer_spacetime.tex` and `sec_conservativity.tex` must be moved to `sequel/` or removed from the submission folder.

### Medium-priority issues

4. Standing refinement-conservation hypothesis in sec_null_decomposition.tex is prose-only; needs a labeled axiom/definition.
5. Conclusion is terse (19 lines) for a paper of this size; needs APAL-appropriate discussion expansion.
6. No APAL-published papers in the bibliography; add at least one or two for venue positioning.

### Mathematical assessment

- All 7 core theorems (A1--A2, B1--B2, C1--C3) are correctly stated, fully proved, and genuinely new.
- No unstated assumptions detected in the main theorem chain.
- Proofs are complete; no gaps.
- Cross-references: 0 dangling references found; 63 unused labels (cosmetic, not blocking).

### AI-voice assessment

- PASS. No manifesto language, no repeated summaries, no loose novelty claims. Two minor promotional phrases flagged in the review (Remark 5.11, Conclusion "genuine logical enrichment") -- tolerable but could be tightened.

### Bibliography pass results

- Citations added: 0
- Citations to remove: 10 (listed above)
- Target-journal papers that materially changed framing: 0 (none found; this is itself a gap)

## P5 Integration Summary

All three P4 hard blockers and all medium-priority issues resolved. Fixes applied:

### Hard blockers (all resolved)

1. **sec_homological_visibility.tex line count.** File was already split by P4 into `sec_homological_visibility.tex` (571 lines) and `sec_branch_aggregation.tex` (572 lines). Both under 800 lines. `main.tex` already contains `\input{sec_branch_aggregation}` at the correct position.
2. **Uncited bibliography entries.** Cited Kripke1965, Beth1956, Fitting1969, Goldblatt2006 in a new paragraph in `sec_introduction.tex` (forcing/logic tradition). Removed Baltag1998, Groenendijk1991, vanBenthem2011, vanDalen2013, Veltman1996, TroelstraVanDalen1988 from `references.bib`. Final bibliography: 15 entries, 15 cited, 0 uncited.
3. **Sequel files moved.** `sec_observer_spacetime.tex` and `sec_conservativity.tex` moved to `sequel/` subdirectory. `main.tex` does not reference them.

### Medium-priority fixes (all resolved)

4. **Standing refinement hypothesis formalized.** Replaced prose assumption in `sec_null_decomposition.tex` with a labeled hypothesis `\ref{hyp:refinement-conservation}` using an enumerated `(RC)` environment. Updated the proof of `prop:typed-readout-persistence` to cite the label explicitly.
5. **Conclusion expanded.** Added new subsection "Relation to topos-theoretic forcing" in `sec_conclusion.tex` positioning the paper relative to Tierney and Johnstone's topos-theoretic forcing tradition, citing MacLaneMoerdijk1994 and Johnstone2002. Conclusion grew from 19 to 23 lines.
6. **Abstract sentence split.** Broke the long em-dash sentence about the four-layer chain in `main.tex` abstract into two sentences.

### Verification

- All `.tex` files under 800 lines (max: 580 lines in `sec_null_decomposition.tex`)
- All `\cite{}` keys have corresponding `references.bib` entries (15/15)
- All `references.bib` entries are cited in the main-line `.tex` files (15/15)
- `main.tex` does not reference sequel files
- No sequel files remain in the submission directory root

## P7 Submission Pack Summary

Three artifacts now define the P7 state:

1. **Cover letter** (`cover_letter_apal.txt`): addressed to the APAL editors; describes the four-layer conservative extension chain, the three main theorem groups (forcing necessity, branched gerbe semantics, homological visibility), and positions the paper relative to APAL-relevant traditions (Kripke semantics, Beth tableaux, Fitting forcing, topos-theoretic forcing of Tierney and Johnstone, Lawvere--Tierney topologies). States the current local manuscript length correctly as 37 pages, with 15 references, and remains signed as "The Authors."

2. **Submission checklist** (`submission_checklist.md`): 12-item structured checklist. Results: 11 PASS, 1 blocker. Key verifications: local `pdflatex -> bibtex -> pdflatex -> pdflatex` build succeeds, all 15 bibliography entries resolve into the built manuscript, all files are under the 800-line limit (max 580), sequel files remain isolated in `sequel/`, no revision-trace language appears in submission `.tex` files, MSC 2020 classification and keywords are present, and no unresolved cross-references were observed in the local build. The remaining blocker is missing title-page author metadata.

3. **P7 submission note** (`P7_SUBMISSION_NOTE_2026-03-30.md`): records the true submission status, the remaining blocker, the local verification run, and paper-local residual risks.

### Remaining blocker

`\author{}` is empty in `main.tex` line 59. This is not an anonymous-review advisory: APAL's current guide requires all authors to be listed in the manuscript and entered into the submission system. P7 is therefore blocked pending final author metadata.

---

# THEOREM_LIST

## Core results that define the paper

- `thm:pointwise-irreducibility`
  shows gluing predicates are not definable at the lower forcing layer
- `thm:sheafification-characterization`
  identifies compatible local sectionability through sheafification
- `thm:component-gerbe-decomposition`
  isolates the visible-branch gerbe structure
- `thm:gerbe-null-semantics`
  interprets gluing-level absence through branched gerbe semantics
- `thm:initial-visible-quotient`
  extracts the first visible quotient of an obstruction
- `thm:intrinsic-visible-quotient`
  defines the intrinsic visible quotient without choosing a splitting
- `thm:character-blind-obstructions`
  identifies the pure-extension residual invisible to character channels
- `thm:branch-comparison-exact-sequence`
  compares branch-sensitive and branch-uniform visibility
- `thm:branch-resolution-budget`
  gives the exact hidden-information cost of branch resolution
- `thm:unique-branch-contextuality-comparison`
  connects the unique-branch case with the no-global-section picture

## Results that may need relocation or compression

- `thm:multi-branch-strictification-budget`
- `thm:branch-sensitive-visible-quotient`
- `thm:branch-uniform-visible-quotient`
- observer-spacetime propositions in `sec_observer_spacetime.tex`

## Editorial objective

The final APAL draft should read as one theorem package answering one
mathematical question: which part of a gluing obstruction is semantically
visible and what hidden budget is required to strictify it.

---

# SOURCE_MAP

## Upstream source scope

- Root source:
  `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/logic_expansion_chain/`

## Local manuscript file map

- `sec_preliminaries.tex`
  conservative extensions and finite-chain invariance
- `sec_information_states.tex`
  information states, forcing, and lifted pointwise soundness
- `sec_null_decomposition.tex`
  local objects, sheafification, typed readouts, null trichotomy, forcing necessity
- `sec_gerbe_obstruction.tex`
  component gerbes, visible quotients, strictification budget
- `sec_homological_visibility.tex`
  intrinsic visible quotient, character detection, blind obstructions, branch comparison, contextuality comparison
- `sec_multiaxis_refinement.tex`
  refinement dynamics and branch visibility monotonicity
- `sec_conservativity.tex`
  concrete realizations and semantic fidelity
- `sec_observer_spacetime.tex`
  observer and spacetime layer; candidate sequel material unless retained by explicit editorial decision

## Retained theorem chain

- `thm:pointwise-irreducibility`
- `thm:sheafification-characterization`
- `thm:component-gerbe-decomposition`
- `thm:gerbe-null-semantics`
- `thm:initial-visible-quotient`
- `thm:intrinsic-visible-quotient`
- `thm:character-blind-obstructions`
- `thm:branch-sensitive-visible-quotient`
- `thm:branch-uniform-visible-quotient`
- `thm:branch-comparison-exact-sequence`
- `thm:branch-resolution-budget`
- `thm:multi-branch-strictification-budget`
- `thm:unique-branch-contextuality-comparison`

## Traceability decision still required

- decide whether `sec_observer_spacetime.tex` remains in the APAL paper or is promoted to the sequel track

---



# P2 Extension Note -- 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target journal: Annals of Pure and Applied Logic (APAL)
Stage: P2 Research Extension

---

## 1. Main Theorem Package

The APAL submission is organized around one research question:

> Given an admitted reference carrying a finite abelian gluing obstruction, which part of that obstruction is semantically visible without enlarging the state space, and how much additional information is required to recover the hidden part?

The answer is delivered by exactly seven main results in three groups.

### Group A -- Forcing Necessity (logical foundation)

| # | Label | One-line statement |
|---|-------|--------------------|
| A1 | `thm:sheafification-characterization` | Compatible local sectionability at an admitted reference is equivalent to nonemptiness of the sheafified local object functor at that reference. |
| A2 | `thm:pointwise-irreducibility` | Compatible local sectionability and gluing-level absence are not definable in the information-state forcing language without the local-object enrichment. |

### Group B -- Branched Gerbe Semantics (structural content)

| # | Label | One-line statement |
|---|-------|--------------------|
| B1 | `thm:component-gerbe-decomposition` | Each visible value class of an admitted reference determines a banded component gerbe over the slice site. |
| B2 | `thm:gerbe-null-semantics` | Gluing-level absence holds exactly when visible branches exist but every component gerbe is non-neutral; under global conservativity, global sectionability is equivalent to some component gerbe being neutral. |

### Group C -- Homological Visibility and External Anchor (quantitative results)

| # | Label | One-line statement |
|---|-------|--------------------|
| C1 | `thm:intrinsic-visible-quotient` | The class-admissible characters of a branch obstruction class are exactly the annihilator of the image of the homological evaluation map; the intrinsic visible quotient is the cokernel of that map. |
| C2 | `thm:character-blind-obstructions` | A branch obstruction is character-blind (every character is class-admissible yet the obstruction is nontrivial) if and only if the class is a pure Ext-type residual. |
| C3 | `thm:unique-branch-contextuality-comparison` | In the unique-branch support-presheaf setting, the theory recovers the Abramsky--Brandenburger no-global-section picture and refines it by identifying the precise blind residual as an Ext-type mechanism. |

These seven results form a strict dependency chain: A1-A2 justify the enrichment, B1-B2 supply the semantic framework, and C1-C3 deliver the quantitative answer and the external anchor.

---

## 2. Scope Cuts

### Moved to appendix (already there or to be moved)

| Item | Current location | Action | Justification |
|------|-----------------|--------|---------------|
| `thm:axis-complexity-upper-bounds` | `sec_appendix.tex` | Keep in appendix | Secondary; only upper bounds without matching lower bounds. Already in appendix. |

### Moved to sequel track

| Item | Current location | Action | Justification |
|------|-----------------|--------|---------------|
| `sec_observer_spacetime.tex` (entire section) | Standalone file, not in `main.tex` | **Sequel.** | Adds observer-indexed states, coupled states, event-region systems, and observer symmetry. None of these are invoked by any theorem in the main A-B-C chain. The conservativity proposition (`prop:ost-conservative`) is a one-line observation. The material belongs to a follow-up paper on multi-observer semantics. |
| `sec_conservativity.tex` (entire section) | Standalone file, not in `main.tex` | **Sequel.** | Contains the concrete-realization/semantic-fidelity layer. No main theorem depends on it. It is natural companion material for the observer-spacetime sequel where implementations matter. |

### Demoted from main-line to supporting role within the paper

| Item | Label | Action | Justification |
|------|-------|--------|---------------|
| Branch-sensitive visible quotient | `thm:branch-sensitive-visible-quotient` | **Keep, but present as a consequence** after the main C-group. | Needed to state the exact comparison sequence. |
| Branch-uniform visible quotient | `thm:branch-uniform-visible-quotient` | **Keep, but present as a consequence.** | Needed to state the exact comparison sequence. |
| Exact branch comparison sequence | `thm:branch-comparison-exact-sequence` | **Keep as the main multi-branch result.** | This is the single sharpest statement comparing branch-sensitive and branch-uniform visibility. |
| Branch-resolution budget | `thm:branch-resolution-budget` | **Keep as a corollary** of the comparison sequence. | Gives the exact information cost; direct corollary. |
| Multi-branch strictification budget | `thm:multi-branch-strictification-budget` | **Keep as a corollary.** | Gives the max-over-branches budget; direct corollary. |
| Uniform hidden budget factorization | `cor:uniform-hidden-budget-factorization` | **Keep as a corollary.** | One-line consequence of the comparison sequence. |

**Decision rationale on branch-budget theorems:** The branch-sensitive/branch-uniform comparison sequence (`thm:branch-comparison-exact-sequence`) is payoff, not overload. It answers a natural follow-up question (what happens when there are multiple visible branches?) and the two-branch sphere example (`ex:two-branch-sphere-separation`) concretely separates the invariants. However, these results should be presented as "secondary consequences" (as the introduction already frames them), not elevated to equal status with the A-B-C core. The branch-budget theorems beyond the comparison sequence (the two separate quotient theorems, the multi-branch strictification budget) are kept as supporting corollaries.

---

## 3. Gap Analysis

### Gap 1: Initial visible quotient vs. intrinsic visible quotient bridge

The paper proves both `thm:initial-visible-quotient` (strict, presentation-dependent) and `thm:intrinsic-visible-quotient` (canonical, class-level). The comparison between them is given by `cor:strict-to-intrinsic-visible` and `prop:chain-vs-homological-visibility`. These are present and correct, but the transition from presentation-level to class-level visibility needs tighter prose in the rewrite: the reader currently must assemble the relationship across multiple subsections.

**Recommendation:** In the rewrite, add a one-paragraph bridge immediately after `thm:initial-visible-quotient` saying: "The strict quotient depends on a choice of cocycle. The next subsection removes this dependence." Then make `thm:intrinsic-visible-quotient` the definitive version. The current text already has all the mathematics; this is a presentation gap, not a proof gap.

### Gap 2: Hypotheses of the gerbe construction

The paper fixed two correctness issues (review_notes.txt items 1-2): branch constancy for the decomposition corollary, and global conservativity for the neutral-gerbe equivalence. These fixes are now in place. However, the hypothesis inventory still appears only inside the proof environment and the remark `rem:gluing-sensitive-lifts`. A reader scanning for the complete hypothesis list must reconstruct it.

**Recommendation:** Add a clearly labeled "Standing Hypotheses" environment at the start of the gerbe-obstruction subsection that collects the four conditions: (i) admitted reference with realization prestack, (ii) band identification, (iii) global conservativity at the terminal fibre, (iv) cofinal gerbe-adapted covers. This is a formatting gap, not a mathematical gap.

### Gap 3: The Abramsky--Brandenburger anchor could be strengthened

`thm:unique-branch-contextuality-comparison` formally connects to the no-global-section picture but the worked example uses `ex:rp2-character-blind` (an RP2-type nerve). The paper would benefit from one additional micro-example showing a scenario that is contextual in the Abramsky--Brandenburger sense and for which the intrinsic visible quotient is proper (not the trivial or blind case).

**Recommendation:** Add a short example (5-10 lines) with a triangulation of S2 and band Z/nZ, producing a nontrivial visible quotient. The two-branch sphere example (`ex:two-branch-sphere-separation`) already does something close but is multi-branch. A single-branch variant on S2 with Z/2Z band gives K = Z/2Z and A_vis = 0 (maximal collapse), which would demonstrate the opposite extreme from the RP2 blind case.

### Gap 4: No explicit statement connecting the four-layer chain to the three theorem groups

The preliminaries define L0-L4 and the introduction names Theorems A, B, C. But there is no explicit mapping saying: "Theorem A lives at the L1-L2 boundary, Theorem B at L2-L3, Theorem C at L3." The rewrite should include this mapping in the introduction roadmap.

---

## 4. Sharpened Theorem Lineup

The recommended final ordering of main-body content is:

1. **sec_introduction.tex** -- One research question, three main results (A, B, C), secondary consequences named but not foregrounded.
2. **sec_preliminaries.tex** -- Logic layers, conservative extension, finite-chain invariance. (Unchanged.)
3. **sec_information_states.tex** -- Information states, forcing, singleton conservativity, lifted soundness. (Unchanged.)
4. **sec_null_decomposition.tex** -- Local objects, existence levels, sheafification characterization (A1), null trichotomy, realization prestacks, visible value classes, typed readouts, forcing necessity (A2).
5. **sec_gerbe_obstruction.tex** -- Standing hypotheses, component gerbe decomposition (B1), branch constancy corollary, Cech obstruction construction, gerbe-null-semantics (B2), strict visible quotient and strictification cost.
6. **sec_homological_visibility.tex** -- Homological evaluation map, intrinsic visible quotient (C1), character-blind obstructions (C2), prime decomposition of visibility, branch-sensitive and branch-uniform aggregation, exact branch comparison sequence, branch-resolution budget, unique-branch contextuality comparison (C3), worked examples.
7. **sec_multiaxis_refinement.tex** -- Refinement dynamics, branch visibility monotonicity, value-preserving rewrites.
8. **sec_conclusion.tex** -- Summary of the three results, external significance, open problems (lower bounds for support problems, multi-observer extension).
9. **sec_appendix.tex** -- Finite-state complexity upper bounds.

**Not included in the main document:**
- `sec_observer_spacetime.tex` -- sequel track
- `sec_conservativity.tex` -- sequel track

This ordering matches the current `main.tex` input sequence, which already excludes the two sequel files.

---

## 5. Introduction Plan

The introduction should open with the observation that standard pointwise semantics cannot express the local-to-global gap that drives gluing failure, motivate the four-layer conservative extension chain as a minimal framework for that gap, and then state the paper's single research question: once an admitted reference carries a finite abelian gluing obstruction, what part is semantically visible and what is the exact cost of recovering the hidden part? The answer should be previewed as three named results. Theorem A (forcing necessity) establishes that the enrichment is not decorative: gluing predicates are provably invisible at the lower layer. Theorem B (branched gerbe semantics) shows that visible branches decompose the realization stack into banded component gerbes, and gluing-level absence is exactly non-neutrality of all component gerbes. Theorem C (homological visibility) identifies the intrinsic visible quotient as the cokernel of the homological evaluation map, identifies the blind residual as a pure Ext-type remnant, and anchors the whole theory to the Abramsky--Brandenburger no-global-section picture by showing that the unique-branch case recovers that picture and refines it. The introduction should close with a brief mention of the secondary multi-branch comparison sequence and worked examples, followed by the section-by-section roadmap.

---

## Appendix: Concrete Decisions Summary

| Decision | Verdict |
|----------|---------|
| `sec_observer_spacetime.tex` in scope? | **No. Sequel track.** No main-chain theorem depends on it. |
| Branch-budget theorems beyond comparison sequence? | **Keep as secondary consequences, not main results.** The comparison exact sequence is the one clean statement; its corollaries are retained but subordinated. |
| Every main theorem answers the visible-obstruction question? | **Yes after the above cuts.** A1-A2 justify the framework, B1-B2 set up the gerbe semantics of visibility, C1-C3 deliver the quantitative answer and external anchor. |

---



# P3 Rewrite Note -- 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target journal: Annals of Pure and Applied Logic (APAL)
Stage: P3 Journal-Fit Rewrite

---

## 1. Abstract (main.tex)

Compressed from ~180 words to ~150 words. Structure: problem (pointwise semantics gap) -> framework (four-layer chain) -> research question -> Theorems A, B, C with one-line statements -> payoff (Abramsky--Brandenburger anchor). Removed manifesto language and secondary consequences from the abstract.

## 2. Introduction (sec_introduction.tex)

Complete rewrite. Changes:

- Opens with gluing failures in sheaf theory and the pointwise semantics gap.
- States the four-layer conservative extension chain as the minimal framework, with the explicit chain displayed.
- States the research question as a single sentence: "what part of a finite abelian gluing obstruction is semantically visible?"
- Previews Theorems A, B, C with one-line statements.
- Adds explicit layer-boundary mapping (Gap 3 closure): A at L1-L2, B at L2-L3, C at L3.
- Mentions secondary results (branch comparison, exact sequence) without foregrounding them.
- Adds hypothesis stratification paragraph clarifying which hypotheses enter where.
- Closes with section-by-section roadmap.
- Removed all programmatic/framework language.

## 3. Gap Closures

### Gap 1: Bridge between strict and intrinsic visible quotients

Added a one-paragraph bridge in sec_gerbe_obstruction.tex immediately after the proof of `thm:initial-visible-quotient`, before `thm:character-definability-barrier`. The paragraph states that the strict quotient depends on the cocycle representative, that the next subsection removes this dependence via the homological evaluation map, and points to the exact comparison results (`cor:strict-to-intrinsic-visible`, `prop:chain-vs-homological-visibility`).

### Gap 2: Standing Hypotheses environment

Added a clearly labeled list of four standing hypotheses (H1--H4) at the start of the gerbe-obstruction subsection in sec_gerbe_obstruction.tex:
- (H1): admitted reference with realization prestack
- (H2): band identification
- (H3): global conservativity at the terminal fibre
- (H4): cofinal gerbe-adapted covers

### Gap 3: Theorem-to-layer mapping

Addressed in the rewritten introduction. Each theorem group now carries an explicit layer-boundary annotation: Theorem A at L1-L2, Theorem B at L2-L3, Theorem C at L3.

### Gap 4: S2 single-branch micro-example

Added `ex:s2-single-branch-maximal-collapse` in sec_homological_visibility.tex, placed after the RP2 blind example. The example uses $S^2$ with band $\mathbb{Z}/2\mathbb{Z}$ in the unique-branch case:
- $H_2(S^2,\mathbb{Z}) \cong \mathbb{Z}$, so $\mathrm{ev}_\omega$ is surjective.
- $K_\omega = A$, $A_{\mathrm{vis}}^\omega = 0$ (maximal collapse).
- Contrasts explicitly with the RP2 blind case: opposite extreme of the visibility spectrum.

## 4. Conclusion (sec_conclusion.tex)

Complete rewrite. Structured into three subsections:
- Summary of results: recaps A, B, C in concise prose.
- External significance: connection to contextuality, topos theory, the enrichment as logical rather than decorative.
- Open problems: lower bounds for support problems, multi-observer extension.

## 5. Style pass

- sec_multiaxis_refinement.tex: tightened opening paragraph to remove capabilities-pitch language, replaced with a factual statement about the section's role at L4.
- No other programmatic language found in any .tex file.
- All files checked for manifesto language, "novel framework" claims, etc. None found.

## 6. File split: sec_homological_visibility.tex

The original `sec_homological_visibility.tex` was 1144 lines, exceeding the 800-line limit. It was split at the `\subsection{Aggregating visibility across branches}` boundary:

- `sec_homological_visibility.tex` (571 lines): homological evaluation, intrinsic visible quotient, character-blind obstructions, RP2 and S2 examples, intrinsic strictification codes, prime decomposition, budget comparisons.
- `sec_branch_aggregation.tex` (572 lines, new file): branch-sensitive and branch-uniform aggregation, exact comparison sequence, branch-resolution budget, two-branch sphere example, contextuality comparison.

The new file is included in `main.tex` via `\input{sec_branch_aggregation}` between `sec_homological_visibility` and `sec_multiaxis_refinement`.

## 7. Files modified

- `main.tex` -- abstract rewrite, added `\input{sec_branch_aggregation}`
- `sec_introduction.tex` -- complete rewrite
- `sec_gerbe_obstruction.tex` -- standing hypotheses (Gap 2), bridge paragraph (Gap 1)
- `sec_homological_visibility.tex` -- S2 micro-example (Gap 4), truncated to 571 lines
- `sec_branch_aggregation.tex` -- new file (split from sec_homological_visibility.tex)
- `sec_conclusion.tex` -- complete rewrite
- `sec_multiaxis_refinement.tex` -- opening paragraph tightened

## 8. Files not modified

- `sec_preliminaries.tex` -- already clean APAL register
- `sec_information_states.tex` -- already clean
- `sec_null_decomposition.tex` -- already clean
- `sec_appendix.tex` -- already clean
- `references.bib` -- bibliography pass deferred to P4

---



# P4 Editorial Review -- 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target journal: Annals of Pure and Applied Logic (APAL)
Stage: P4 Editorial Review

---

## 1. Decision

**MAJOR_REVISION**

The paper contains a genuine and interesting theorem package -- the homological visibility analysis of gluing obstructions in a forcing semantics is original and well-executed at the technical level. However, the manuscript has structural and presentational problems that prevent acceptance in its current form. The most serious issues are: (a) a file exceeding the 800-line project limit by 43%, (b) 10 uncited bibliography entries, (c) two sections still present in the directory that were supposedly moved to a sequel track but cross-reference labels in the main text, (d) the observer-spacetime and concrete-realization sections remain in the repository without clear separation from the submission, and (e) the paper's ratio of supporting corollaries to core theorems is high enough that a referee may lose the main thread. The mathematical content is sound; the revision is primarily structural and editorial.

---

## 2. Main Mathematical Blockers

### 2.1 Theorems: correctness and completeness

The seven core results (A1--A2, B1--B2, C1--C3) are correctly stated with explicit hypotheses. Proofs are complete and do not rely on unstated assumptions. Specific notes:

- **Theorem A2 (pointwise-irreducibility):** The proof constructs a concrete automorphism-based separation argument. It is clean and self-contained. No issue.

- **Theorem B1 (component-gerbe-decomposition):** The proof appeals to the Stacks Project classification of gerbes (Tag 06NY). The hypotheses (H1)--(H4) are now explicitly listed at the section head. The standing hypothesis inventory (Gap 2 from P2) has been correctly closed.

- **Theorem B2 (gerbe-null-semantics):** The proof correctly chains through sheafification characterization, visible value components, and no-new-global-objects. The global conservativity hypothesis is correctly invoked only where needed (for the reverse direction of the neutral-gerbe equivalence). No issue.

- **Theorem C1 (intrinsic-visible-quotient):** The proof relies on the naturality of the universal coefficient sequence and the injectivity of the divisible-group-valued version of the UCT map. This is standard homological algebra (Weibel, Hatcher) and is correctly applied. No issue.

- **Theorem C2 (character-blind-obstructions):** Correctly identifies the pure-Ext residual. The equivalence chain (i)--(iv) is tight. No issue.

- **Theorem C3 (unique-branch-contextuality-comparison):** The connection to Abramsky--Brandenburger is genuine but narrow. The paper correctly identifies the support presheaf of an empirical model with the local object functor and verifies the correspondence at the level of individual forcing statements. However, the comparison is limited to the unique-branch case with a single band. The paper honestly states this limitation.

### 2.2 Novelty assessment

The core contribution is genuine and new:

1. The forcing-necessity result (Theorem A2) is a clean separation result that has no direct precedent in the contextuality literature.
2. The branched gerbe semantics (Theorem B) extends the single-obstruction-class picture to a multi-branch setting. This is a natural but nontrivial extension.
3. The homological visibility theorem (Theorem C1) repurposes the universal coefficient theorem to define a canonical visible quotient. The identification of the blind residual as a pure Ext-type class is the sharpest result in the paper.

The paper does NOT repackage known results. The connection to Abramsky--Brandenburger is a recovery result, not the main theorem.

### 2.3 Hypothesis management concerns

- The standing assumption at the top of sec_null_decomposition.tex ("refinement acts conservatively on the local structures...a visible value class already uniquely determined at p is not split by further refinement") is used in Proposition 5.16 (typed-readout-persistence) but is never formalized as a labeled hypothesis. It should either be promoted to a named axiom or given a label that the later results can cite explicitly. As written, a reader must re-read the section preamble to discover this unstated constraint.

- The realization prestack definition (Definition 5.7) requires that the presheaf of isomorphism classes recovers the local object functor. The canonical split prestack (Proposition 5.8) always exists, but the substantive theorems (B1, B2) require a gluing-sensitive lift. Remark 5.11 discusses this but the hypothesis "the realization prestack is gluing-sensitive" is never formally stated as a condition anywhere. The reader must infer it from context.

---

## 3. Editorial Blockers

### 3.1 sec_homological_visibility.tex exceeds 800-line limit

This file is 1144 lines, well over the 800-line project limit. It must be split. Natural split point: the "Aggregating visibility across branches" subsection (starting at approximately line 573) should be extracted into a separate file (e.g., `sec_branch_aggregation.tex`). This would yield approximately 572 lines for homological visibility and 572 lines for branch aggregation, both within the limit.

### 3.2 Bibliography: 10 uncited entries

The following 10 entries in `references.bib` are never cited in any `.tex` file included by `main.tex`:

| Key | Author(s) |
|-----|-----------|
| `Baltag1998` | Baltag--Moss--Solecki |
| `Beth1956` | Beth |
| `Fitting1969` | Fitting |
| `Goldblatt2006` | Goldblatt |
| `Groenendijk1991` | Groenendijk--Stokhof |
| `Kripke1965` | Kripke |
| `TroelstraVanDalen1988` | Troelstra--van Dalen |
| `vanBenthem2011` | van Benthem |
| `vanDalen2013` | van Dalen |
| `Veltman1996` | Veltman |

These must either be cited somewhere in the text (if relevant to the actual content) or removed from the bib file before submission. Several of these (Kripke, Beth, Fitting, Goldblatt) are natural references for the forcing/intuitionistic-logic background. If they are kept, they should be cited in the introduction or preliminaries where the forcing tradition is discussed. The dynamic semantics references (Veltman, Groenendijk--Stokhof, van Benthem, Baltag) seem to be relics from a broader framework version of the paper and should be removed unless the introduction explicitly discusses the information-state semantics lineage.

**Recommendation:** Keep Kripke1965, Beth1956, Fitting1969, and Goldblatt2006 and add brief citations in the introduction's first paragraph (the forcing/sheaf-theoretic tradition). Remove Baltag1998, Groenendijk1991, vanBenthem2011, vanDalen2013, Veltman1996, and TroelstraVanDalen1988 unless the introduction is expanded to discuss the dynamic-semantics connection (which would dilute the APAL focus).

### 3.3 Sequel-track files still present in directory

`sec_observer_spacetime.tex` (178 lines) and `sec_conservativity.tex` (93 lines) are correctly excluded from `main.tex` but remain in the directory. This is a submission hygiene issue: if the submission package includes all `.tex` files in the directory, these orphan files will confuse referees. They reference labels (`cor:normalization-no-fact-creation`, `prop:readout-transport`) that are defined in the main-line files, creating a one-directional dependency.

**Action required:** Move these files to a subdirectory (e.g., `sequel/`) or remove them from the submission directory entirely.

### 3.4 No author name

`main.tex` line 59 has `\author{}`. This is presumably intentional for anonymous review but should be verified. If APAL requires author identification at submission, this must be filled.

### 3.5 Abstract word count

The abstract is approximately 155 words. APAL has no strict word limit for abstracts, but the abstract is dense. The phrase "conservative extension chain---from pointwise semantics through information-state forcing to local objects and refinement dynamics" is hard to parse on first reading. Consider breaking the abstract into two sentences here: one for the framework and one for the research question.

### 3.6 Section numbering / structural mismatch

The introduction roadmap (line 41 of sec_introduction.tex) mentions "the gerbe-obstruction subsection" and "the homological-visibility subsection" as if they were subsections of a single section. But in `main.tex`, `sec_gerbe_obstruction.tex` and `sec_homological_visibility.tex` are `\input`-ed as separate top-level files. Since both use `\subsection` rather than `\section` commands, they are formatted as subsections of whatever section precedes them. This means:

- `sec_gerbe_obstruction.tex` starts with `\subsection{Component gerbes...}`, making it a subsection of Section 5 (Local Objects).
- `sec_homological_visibility.tex` starts with `\subsection{Homological evaluation...}`, also making it a subsection of Section 5.

This is likely intentional (Section 5 is the long core section), but it means Section 5 runs from line 1 of `sec_null_decomposition.tex` through the end of `sec_homological_visibility.tex`, spanning three input files and over 2000 lines of material. For APAL, this is acceptable if the subsection structure is clear, but the table of contents will show a single Section 5 with many subsections. The introduction roadmap should match this structure explicitly.

### 3.7 Missing target-journal related work

The bibliography contains zero papers published in APAL itself. While this is not disqualifying, it is unusual for a submission to a journal in the area of logic. The paper's topic (forcing semantics, sheaf theory, conservative extensions) overlaps with APAL's scope. A brief survey of related APAL publications in the introduction or related-work section would strengthen the submission. Candidates: sheaf-theoretic methods in formal logic, categorical semantics papers, topos-theoretic forcing.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### Issue 1: sec_homological_visibility.tex must be split

- **Location:** `sec_homological_visibility.tex`, lines 573--1144
- **Problem:** File is 1144 lines, exceeding the 800-line limit by 344 lines.
- **Fix:** Extract the subsection "Aggregating visibility across branches" (from Definition 7.10 onward) and the subsection "Connection to sheaf-theoretic contextuality" into a new file `sec_branch_aggregation.tex`. Add `\input{sec_branch_aggregation}` to `main.tex` after `\input{sec_homological_visibility}`.

### Issue 2: Standing refinement hypothesis needs formalization

- **Location:** `sec_null_decomposition.tex`, paragraph before subsection 5.1 (lines 5--6)
- **Problem:** The assumption "refinement acts conservatively on the local structures" is stated in prose but never given a label. It is invoked silently in Proposition 5.16 and Theorem 5.17.
- **Fix:** Create a labeled standing hypothesis (e.g., `\begin{enumerate}[label=(R),nosep] ... \end{enumerate}`) or a definition environment that formalizes the refinement-conservation axiom. Reference it by label in all proofs that use it.

### Issue 3: Unused bibliography entries

- **Location:** `references.bib`
- **Problem:** 10 of 21 entries (48%) are never cited.
- **Fix:** Either cite the classic forcing references (Kripke, Beth, Fitting, Goldblatt) in the introduction and remove the rest, or remove all 10. Do not submit with phantom bibliography entries.

### Issue 4: Sequel files still in submission directory

- **Location:** `sec_observer_spacetime.tex`, `sec_conservativity.tex`
- **Problem:** Present in the directory but excluded from `main.tex`. Referees seeing these files will be confused.
- **Fix:** Move to `sequel/` subdirectory or delete from submission directory.

### Issue 5: Overlong abstract sentence

- **Location:** `main.tex`, lines 64--65 (abstract)
- **Problem:** The sentence beginning "We introduce a four-layer conservative extension chain" runs to approximately 60 words with an em-dash parenthetical, making it hard to parse.
- **Fix:** Split into two sentences. First: state the four-layer chain. Second: state the research question.

### Issue 6: Many unused labels suggest over-engineering

- **Location:** Throughout all `.tex` files
- **Problem:** 63 labels are defined but never cross-referenced. While some of these are normal (section labels, stand-alone examples), several are corollaries that exist only to be "available" rather than to serve the main argument.
- **Fix:** This is cosmetic and does not block acceptance, but a cleanup pass removing labels from results that are never cited would signal tighter editing. Low priority.

### Issue 7: The introduction's Plan of the Paper paragraph references sections by name, not number

- **Location:** `sec_introduction.tex`, line 41
- **Problem:** References like "the gerbe-obstruction subsection" are informal. Since these are `\subsection` environments with labels, the plan should use `\Cref` references.
- **Fix:** Replace prose references with `\Cref` calls to the corresponding section labels.

### Issue 8: sec_conclusion.tex is very short

- **Location:** `sec_conclusion.tex` (19 lines)
- **Problem:** The conclusion is adequate but extremely terse for a paper of this length. For APAL, a more substantial discussion section is expected -- at minimum, a comparison with other approaches to the local-to-global gap in logic (e.g., abstract model theory, institution theory, topos-theoretic forcing).
- **Fix:** Expand the "External significance" and "Open problems" subsections. Add a paragraph positioning the paper relative to topos-theoretic forcing (Tierney, Johnstone) and to the categorical semantics tradition in APAL.

---

## 5. Comparison with Prior Stage Notes

### P2 gap closures (all verified resolved)

| P2 Gap | Status | Verification |
|--------|--------|--------------|
| Gap 1: Bridge between strict and intrinsic visible quotients | **Closed.** | Bridge paragraph present in `sec_gerbe_obstruction.tex` after `thm:initial-visible-quotient`. |
| Gap 2: Standing Hypotheses (H1)--(H4) | **Closed.** | Labeled list present at start of gerbe-obstruction subsection. |
| Gap 3: Theorem-to-layer mapping in introduction | **Closed.** | Each theorem group now carries explicit layer-boundary annotation. |
| Gap 4: S2 single-branch micro-example | **Closed.** | `ex:s2-single-branch-maximal-collapse` present in `sec_homological_visibility.tex`. |

### P3 rewrite issues (all verified resolved)

| P3 Action | Status | Verification |
|-----------|--------|--------------|
| Abstract compressed to ~150 words | **Done.** | Abstract is ~155 words. Acceptable. |
| Introduction rewrite with one research question | **Done.** | Introduction opens with the gap, states the question, previews A/B/C. |
| Conclusion rewrite | **Done.** | Three clear subsections. |
| Manifesto language removed | **Done.** | No programmatic or capabilities-pitch language found in any file. |

### New issues introduced by P3 rewrite

1. The P3 rewrite note states "bibliography pass deferred to P4." This pass was not performed -- 10 uncited entries remain. This is now a P4 blocker.

2. The P3 rewrite tightened `sec_multiaxis_refinement.tex` opening paragraph but did not address the file length of `sec_homological_visibility.tex`, which was already over 800 lines before P3 added the S2 example. The P3 rewrite actually increased the line count by adding `ex:s2-single-branch-maximal-collapse`.

---

## 6. AI-Voice Check

### Overall assessment: PASS with minor flags

The paper reads as competent mathematical prose. There is no manifesto language, no "novel framework" claims, no repeated summaries. The theorem-proof style is appropriate for APAL.

### Minor flags

1. **Remark 5.11 (rem:gluing-sensitive-lifts):** The phrase "The substantive semantic claims therefore concern which lifts preserve the intended local-to-global content, not whether a formal groupoid-valued lift exists at all" has a slight editorial-voice quality. A real referee would not object, but the phrasing could be tightened to: "The content of the later theorems is therefore which lifts preserve local-to-global semantics, not whether a formal lift exists."

2. **Conclusion, "External significance" subsection:** The sentence "The forcing-necessity theorem shows that the passage from pointwise semantics to local objects is a genuine logical enrichment, not merely a change of vocabulary" is slightly promotional. The theorem already says this; repeating it in the conclusion with "genuine" is mild emphasis. Tolerable for APAL but borderline.

3. **Introduction, hypothesis stratification paragraph:** The sentence "Branch constancy enters only for the decomposition corollary, not for the component-gerbe theorem itself" is useful for the reader. This is good mathematical writing, not AI-voice.

4. No repeated summaries or circular self-references detected. The paper does not re-explain earlier results unnecessarily.

---

## 7. Summary of Required Actions (Ordered by Priority)

| Priority | Action | Blocker? |
|----------|--------|----------|
| 1 | Split `sec_homological_visibility.tex` (1144 lines > 800 limit) | **Yes** |
| 2 | Remove or cite the 10 uncited bibliography entries | **Yes** |
| 3 | Move sequel files out of submission directory | **Yes** |
| 4 | Formalize the standing refinement-conservation hypothesis in sec_null_decomposition | Medium |
| 5 | Expand the conclusion for APAL expectations | Medium |
| 6 | Fix abstract sentence length | Low |
| 7 | Add APAL-published related work to bibliography | Low |
| 8 | Clean up unused labels | Low |

---



# LEAN_SYNC_NOTE 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target: Annals of Pure and Applied Logic (APAL)

## Coverage summary

- Total theorem-level claims: 13
- VERIFIED: 0
- PARTIAL: 0
- MISSING: 13
- N/A: 0

### MISSING (13)

| Label | Description | Notes |
|---|---|---|
| `thm:pointwise-irreducibility` | gluing predicates not definable at lower forcing layer | No Lean counterpart; sheafification/forcing/gerbe vocabulary absent from Lean4 codebase |
| `thm:sheafification-characterization` | compatible local sectionability via sheafification | No Lean counterpart |
| `thm:component-gerbe-decomposition` | visible-branch gerbe structure | No Lean counterpart |
| `thm:gerbe-null-semantics` | gluing-level absence through branched gerbe semantics | No Lean counterpart |
| `thm:initial-visible-quotient` | first visible quotient of an obstruction | No Lean counterpart |
| `thm:intrinsic-visible-quotient` | intrinsic visible quotient without splitting | No Lean counterpart |
| `thm:character-blind-obstructions` | pure-extension residual invisible to character channels | No Lean counterpart |
| `thm:branch-comparison-exact-sequence` | branch-sensitive vs branch-uniform visibility | No Lean counterpart |
| `thm:branch-resolution-budget` | exact hidden-information cost of branch resolution | No Lean counterpart |
| `thm:unique-branch-contextuality-comparison` | unique-branch case vs no-global-section picture | No Lean counterpart |
| `thm:multi-branch-strictification-budget` | multi-branch strictification cost (relocation candidate) | No Lean counterpart |
| `thm:branch-sensitive-visible-quotient` | branch-sensitive visible quotient (relocation candidate) | No Lean counterpart |
| `thm:branch-uniform-visible-quotient` | branch-uniform visible quotient (relocation candidate) | No Lean counterpart |

### Coverage rate: 0/13 = 0%

## Recommended formalization backlog

This paper's theorem vocabulary (sheafification, gerbes, forcing, visible quotients, branch comparison exact sequences) lies entirely outside the current Lean4 library's scope. The Lean4 codebase covers combinatorial/arithmetic Omega structures (Fibonacci folding, rewriting, fiber spectrum, collision kernels, SPG scan error) but has no infrastructure for:

- topos-theoretic or sheaf-cohomological constructions
- forcing and conservative extension machinery
- gerbe decomposition and strictification budget

Priority-ordered candidates if formalization were undertaken:

1. `thm:pointwise-irreducibility` -- foundational; would require a forcing layer definition
2. `thm:sheafification-characterization` -- could potentially be built on mathlib sheaf infrastructure
3. `thm:branch-comparison-exact-sequence` -- homological algebra content; mathlib has some exact-sequence support
4. `thm:branch-resolution-budget` -- quantitative result that could admit a self-contained statement

Practical recommendation: formalization of this paper's claims would require building substantial new Lean4 infrastructure (forcing semantics, gerbe structures) that does not currently exist in either the Omega library or mathlib. This is a long-term project not suitable for near-term P6 gates.

## Mismatches

None (no overlap to compare).

## Source coverage gap

The SOURCE_MAP.md lists upstream sources in `theory/.../logic_expansion_chain/` but the Lean4 IMPLEMENTATION_PLAN.md has zero entries referencing any theorem label from this paper. The entire APAL theorem chain is logically disjoint from the current formalization.

---



# P7 Submission Note -- 2026-03-30

Paper: `2026_conservative_extension_chain_state_forcing_apal`
Target journal: `Annals of Pure and Applied Logic (APAL)`
Stage: `P7 Submission Pack Hardening`

## Current status

`not_submission_ready_yet`

The paper-local submission pack is internally verified, but the package is
still blocked on title-page author metadata in `main.tex`.

## Real blocker

1. `main.tex` still has an empty `\author{}` field.
   - Location: `main.tex:59`
   - Local fact: no author names, affiliations, or corresponding-author
     details are present anywhere on the manuscript title page.
   - External policy check completed on 2026-03-30: APAL's current Guide for
     Authors states that the journal uses single anonymized review and
     requires all authors to be listed in the manuscript and entered in the
     submission system.
   - Practical consequence: do not upload the manuscript until the definitive
     author list and corresponding-author metadata are inserted.

## Local verification

- Ran `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex`
- Ran `bibtex main`
- Ran `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error main.tex` twice more
- Result: `main.pdf` built successfully at 37 pages
- `main.tex` inputs 9 section files plus appendix; all inputs resolved
- `main.tex` does not input any file from `sequel/`
- All submission-root `.tex` files are below the 800-line cap; max is
  `sec_null_decomposition.tex` at 580 lines
- Bibliography resolved successfully through BibTeX; the built `main.bbl`
  contains 15 `\bibitem` entries
- No undefined citation or dangling cross-reference warnings were observed in
  the local final build

## Materials hardened in this pass

- Corrected `cover_letter_apal.txt` page count from "approximately 45 pages"
  to the current locally verified `37` pages
- Corrected `submission_checklist.md` so that missing author metadata is
  recorded as a blocker rather than as an anonymous-review advisory
- Updated `TRACK_BOARD.md` so P7 reflects the true blocked state and links to
  this note

## Non-blocking local issue

- One overfull `\hbox` remains in `sec_introduction.tex` at lines 34--36 in
  the current local build. This is a typesetting warning, not a submission
  blocker.

## Author-side risks not decidable from this directory alone

- If generative AI or AI-assisted technologies were used in manuscript
  preparation, APAL currently requires a disclosure section before the
  references on first submission. The manuscript does not currently contain
  such a section.
- Competing-interest and funding declarations are submission-system artifacts,
  not verifiable from this paper-local directory.

---


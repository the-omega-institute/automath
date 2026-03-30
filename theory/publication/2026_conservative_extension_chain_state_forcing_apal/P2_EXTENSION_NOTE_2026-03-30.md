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

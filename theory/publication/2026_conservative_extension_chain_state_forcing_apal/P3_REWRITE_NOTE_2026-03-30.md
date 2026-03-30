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

## 6. Files modified

- `main.tex` -- abstract rewrite
- `sec_introduction.tex` -- complete rewrite
- `sec_gerbe_obstruction.tex` -- standing hypotheses (Gap 2), bridge paragraph (Gap 1)
- `sec_homological_visibility.tex` -- S2 micro-example (Gap 4)
- `sec_conclusion.tex` -- complete rewrite
- `sec_multiaxis_refinement.tex` -- opening paragraph tightened

## 7. Files not modified

- `sec_preliminaries.tex` -- already clean APAL register
- `sec_information_states.tex` -- already clean
- `sec_appendix.tex` -- already clean
- `references.bib` -- bibliography pass deferred to P4

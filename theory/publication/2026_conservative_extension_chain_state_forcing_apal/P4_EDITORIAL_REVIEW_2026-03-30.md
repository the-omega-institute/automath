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

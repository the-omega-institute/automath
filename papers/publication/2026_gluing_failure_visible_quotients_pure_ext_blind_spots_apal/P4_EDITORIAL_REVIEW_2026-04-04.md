# Gate 3 Editorial Review (P4): First Independent Assessment

**Paper:** Gluing Failure, Visible Quotients, and Pure-Ext Blind Spots
**Target journal:** Annals of Pure and Applied Logic (APAL)
**Date:** 2026-04-04
**Reviewer:** Claude (Gate 3 / P4 editorial review, first round)
**Sibling paper:** `2026_conservative_extension_chain_state_forcing_apal` (received MINOR_REVISION at Gate 3)

---

## I. Decision

$$
\boxed{\text{MAJOR\_REVISION}}
$$

**Rationale:** The mathematical content is sound and matches (indeed, is a strict subset of) the sibling paper that received MINOR_REVISION. However, the "_focused" version has severe bibliographic and structural defects that make the current PDF unsubmittable. Seven out of sixteen cited bibliography keys are missing from `references.bib`, producing "[?]" placeholders throughout the compiled PDF. The build log confirms 104 undefined-reference warnings and the PDF was never re-run to resolve cross-references. Additionally, four orphan `.tex` files litter the submission directory, the submission checklist contains false claims, and the "focused narrowing" from the sibling paper was done incompletely -- resulting in a paper that is neither self-contained nor properly compiled. These are fixable but collectively constitute a MAJOR_REVISION because they render the paper non-reviewable in its current state.

---

## II. Main Mathematical Blockers

### II.1. Are theorems correctly stated with all hypotheses?

**Yes, with one caveat.** The theorem statements in this "_focused" version are identical or nearly identical to those in the sibling paper, which was assessed as mathematically sound. Each theorem either explicitly lists its hypotheses or refers back to a definition/assumption by label. The main conditional structure (global conservativity, gluing-sensitive lift, cofinal gerbe-adapted covers) is properly managed through explicit definitions (def:global-conservativity, def:cech-gluing-obstruction, rem:gluing-sensitive-lifts).

**Caveat (same as sibling):** Theorem (thm:pointwise-irreducibility) concludes with "In particular, the predicates CompSec, Sec, Null^glue are not definable in the information-state forcing language without the local-object enrichment." The proof establishes this only for formulas in the restricted Form_1 class via Padoa's automorphism method. The conclusion should be qualified. This was already flagged in the sibling review and remains unfixed here.

### II.2. Are proofs complete or do they rely on unstated assumptions?

**Proofs are complete** for the material included. No proof invokes a result that is not either proved in the paper or cited with a specific reference. The dependency chain is:

- Theorem A: thm:sheafification-characterization relies on Mac Lane-Moerdijk III.2 and Johnstone B2.2. thm:pointwise-irreducibility is self-contained with an explicit model construction.
- Theorem B: thm:component-gerbe-decomposition relies on the Stacks Project definition of gerbe (Tag 06NY). thm:cech-bridge-compatible-realizations uses standard banded gerbe theory (Giraud Ch. IV). thm:gerbe-null-semantics chains earlier results together correctly.
- Theorem C: thm:intrinsic-visible-quotient uses the universal coefficient exact sequence (Hatcher 3.1), divisibility of the circle (Weibel 2.3), and Pontryagin duality for finite abelian groups (Dummit-Foote 5, 12). All steps are explicit.

**However, citations to 7 of these sources are broken** (see Blocker B1 below).

### II.3. Is the main theorem genuinely new, or a repackaging of known results?

**The core contribution (Theorem C) is genuinely original.** The application of the universal coefficient exact sequence to decompose a gerbe obstruction class into an $H_2$-visible part (detected by characters) and a pure Ext-blind residual, yielding the intrinsic visible quotient $A_{\mathrm{vis}}^\omega = \operatorname{coker}(\mathrm{ev}_\omega)$, is new. The identification of Caru-type blind cases as pure Ext-residuals is a clean new result.

Theorems A and B are less novel individually. The sheafification characterization repackages a known fact. The component gerbe decomposition applies standard Giraud theory in a new semantic context. The undefinability result is a clean application of the automorphism method. Their value lies in the framing: they establish the semantic setting in which Theorem C becomes meaningful.

The two worked examples ($S^2$-type nerve with nontrivial visible quotient, $\mathbb{R}P^2$-type nerve with complete character-blindness) effectively demonstrate both extremes.

---

## III. Editorial Blockers

### B1. BLOCKER: Seven missing bibliography entries

**Severity: BLOCKER -- the paper cannot be submitted in this state.**

The following citation keys appear in the .tex files but have no corresponding entries in `references.bib`:

| Citation key | Used in | Content |
|---|---|---|
| `StacksProject` | sec_null_decomposition (lines 169, 231), sec_gerbe_obstruction (lines 46, 112, 122, 220) | Stacks Project (Tags 02ZP, 042Y, 06NY, Sec. 11) |
| `Hatcher2002` | sec_homological_visibility (lines 38, 310, 334, 342) | Hatcher, Algebraic Topology |
| `Weibel1994` | sec_homological_visibility (line 97) | Weibel, Homological Algebra |
| `DummitFoote2004` | sec_homological_visibility (lines 113, 152) | Dummit-Foote, Abstract Algebra |
| `Giraud1971` | sec_gerbe_obstruction (lines 122, 220) | Giraud, Cohomologie non abelienne |
| `Johnstone2002` | sec_null_decomposition (line 104) | Johnstone, Sketches of an Elephant |
| `BerghSchnurer2021` | sec_multiaxis_refinement (line 183) | Bergh-Schnurer (pullback of gerbes) |

The build log confirms 28 "Citation ... undefined" warnings. The resulting PDF shows "[?]" at every occurrence. This is the single most critical defect.

**Note on BerghSchnurer2021:** This citation appears only in `sec_multiaxis_refinement.tex`, which is NOT compiled in the focused version (not in main.tex). So it is a ghost citation in an orphan file and can be ignored -- but only if the orphan files are cleaned up (see B3).

**Fix:** Add the 6 missing entries (excluding BerghSchnurer2021) to `references.bib`. The sibling paper's `references.bib` likely already contains some of them. Then rebuild with the full pdflatex->bibtex->pdflatex->pdflatex cycle.

### B2. BLOCKER: PDF not properly compiled (104 undefined warnings)

**Severity: BLOCKER.**

The build log shows "There were undefined references" and "Label(s) may have changed. Rerun to get cross-references right." The PDF was generated from a single pdflatex pass without bibtex and without re-running. As a result:

- All `\cite` commands show as "[?]" in the PDF
- All `\Cref` commands show as "??" on the first pass (some may resolve on re-run, but many citations will remain broken until bibtex is run)

The README claims "pdflatex -> bibtex -> pdflatex -> pdflatex" was executed, but the log contradicts this: the bibliography was never generated because the .bib file is incomplete.

**Fix:** After fixing B1, run the full build cycle: `pdflatex main && bibtex main && pdflatex main && pdflatex main`.

### B3. MEDIUM: Orphan files in submission directory

**Severity: MEDIUM.**

Four `.tex` files exist in the directory but are NOT `\input`-ed in `main.tex`:

| File | Contains | Status |
|---|---|---|
| `sec_appendix.tex` | Finite-state complexity upper bounds | Orphan; references labels from sec_multiaxis_refinement.tex |
| `sec_multiaxis_refinement.tex` | Refinement dynamics, support, value-preserving rewrites | Orphan; contains `BerghSchnurer2021` citation |
| `sec_observer_spacetime.tex` | Observer-indexed state systems | Orphan |
| `sec_conservativity.tex` | Concrete realizations and semantic fidelity | Orphan |

The submission checklist explicitly states: "No refinement-dynamics or complexity appendix remains in the APAL-focused version." This is true of the compiled PDF but false of the file directory. If submitted to APAL, these files would confuse editors.

**Fix:** Move orphan files to a `_not_submitted/` subdirectory or delete them. If any content from them is needed (e.g., the appendix), add the corresponding `\input` to `main.tex`.

### B4. MEDIUM: Submission checklist contains false/stale claims

The submission checklist says:
- "Theorem 4.26 (component gerbe decomposition)" -- but in this version, the theorem numbering is different (it will be numbered within Section 4, subsection 4.7)
- "Theorem 4.28 (gerbe-null-semantics)" -- same issue
- "No refinement-dynamics or complexity appendix remains" -- orphan files still present (see B3)

**Fix:** Update the submission checklist to reflect the actual numbering after a clean compile, and note that the orphan files should be excluded from submission.

---

## IV. Specific Cut/Merge/Rewrite Recommendations

### IV.1. BLOCKER: Fix bibliography

- **Location:** `references.bib`
- **Problem:** 6 missing entries (StacksProject, Hatcher2002, Weibel1994, DummitFoote2004, Giraud1971, Johnstone2002) cause every citation in the PDF to render as "[?]".
- **Fix:** Add the following entries (format to match existing style):

```
@misc{StacksProject,
  author = {The Stacks Project Authors},
  title  = {The Stacks Project},
  url    = {https://stacks.math.columbia.edu},
  year   = {2024}
}

@book{Hatcher2002,
  author    = {Allen Hatcher},
  title     = {Algebraic Topology},
  publisher = {Cambridge University Press},
  year      = {2002}
}

@book{Weibel1994,
  author    = {Charles A. Weibel},
  title     = {An Introduction to Homological Algebra},
  publisher = {Cambridge University Press},
  year      = {1994}
}

@book{DummitFoote2004,
  author    = {David S. Dummit and Richard M. Foote},
  title     = {Abstract Algebra},
  edition   = {3rd},
  publisher = {Wiley},
  year      = {2004}
}

@book{Giraud1971,
  author    = {Jean Giraud},
  title     = {Cohomologie non ab\'elienne},
  publisher = {Springer},
  series    = {Grundlehren der mathematischen Wissenschaften},
  volume    = {179},
  year      = {1971}
}

@book{Johnstone2002,
  author    = {Peter T. Johnstone},
  title     = {Sketches of an Elephant: A Topos Theory Compendium},
  publisher = {Oxford University Press},
  year      = {2002}
}
```

### IV.2. MEDIUM: Qualify the undefinability conclusion

- **Location:** sec_null_decomposition.tex, Theorem (thm:pointwise-irreducibility), final paragraph (lines 530-538)
- **Problem:** The "In particular" clause asserts unrestricted non-definability, but the proof establishes it only for automorphism-invariant Form_1-formulas. This was flagged in the sibling paper's review and remains unfixed.
- **Fix:** Rewrite the "In particular" to read: "In particular, no formula of the information-state forcing language that is invariant under Form_1-automorphisms and uses none of the local-object predicates can define CompSec, Sec, or Null^glue." Alternatively, add a remark noting that this is the standard Padoa-method-based notion of non-definability.

### IV.3. MINOR: Expand the UCT identification step

- **Location:** sec_homological_visibility.tex, Theorem (thm:intrinsic-visible-quotient) proof, around line 97
- **Problem:** The step "$\eta_{\mathbb{T}}$ is an isomorphism by [def:finite-nerve-presentation]" compresses two claims: (a) $\operatorname{Ext}^1(H_1, \mathbb{T}) = 0$ because $\mathbb{T}$ is divisible, and (b) therefore $\eta_{\mathbb{T}}$ is injective. The text does cite Weibel for (a), but the logical step from (a) to "isomorphism" needs one more sentence noting that the UCT sequence for $\mathbb{T}$ then collapses to a short exact sequence with trivial left term.
- **Fix:** Add after "Weibel1994": "The universal coefficient sequence for coefficients in $\mathbb{T}$ therefore has vanishing left term, so $\eta_{\mathbb{T}}$ is an isomorphism."

### IV.4. MINOR: Section 4 is very long (all technical content in one section)

- **Location:** Section 4 spans pages 5-19 (out of 20) and contains 8 subsections with all three main theorems.
- **Problem:** APAL readers expect a more balanced sectional structure. A single section containing all the main results makes navigation harder.
- **Fix (optional):** Consider promoting sec_gerbe_obstruction and sec_homological_visibility from `\subsection` to `\section`, yielding Sections 4 (Local Objects), 5 (Gerbe Obstruction), 6 (Homological Visibility), 7 (Conclusion). This would better match the three-theorem structure announced in the introduction.

### IV.5. MINOR: Clean up orphan files

- **Location:** Submission directory root
- **Problem:** sec_appendix.tex, sec_multiaxis_refinement.tex, sec_observer_spacetime.tex, sec_conservativity.tex are present but not compiled.
- **Fix:** Move to a `_drafts/` or `_not_submitted/` subdirectory, or delete.

### IV.6. MINOR: Abstract does not mention "team semantics" first-class

- **Location:** main.tex, abstract (line 64)
- **Problem:** The abstract mentions "flat team-style semantics" but the keyword list uses "team semantics" without the modifier. The abstract could better signal the connection for APAL readers in team/inquisitive semantics.
- **Fix:** No action strictly needed, but consider aligning the abstract wording with the keywords.

### IV.7. MINOR: Introduction forward references use \Cref labels that differ from section titles

- **Location:** sec_introduction.tex, line 35
- **Problem:** The introduction says "Section [sec:null-decomposition] develops local objects, sheafification, visible value classes, and the forcing-necessity theorem." But sec_null_decomposition also includes the gerbe obstruction and homological visibility subsections (because they are \subsections). A reader might not expect those to be under that section label.
- **Fix:** If the section structure remains as-is, update the roadmap paragraph to mention that the gerbe and homological visibility material also lives in Section 4 as subsections.

---

## V. Comparison with Sibling Paper and Prior Reviews

### V.1. Relationship to sibling paper

The "_focused" version is a strict subset of the sibling `2026_conservative_extension_chain_state_forcing_apal`. The following sections from the sibling are excluded:

- sec_branch_aggregation (multi-branch comparison, budget calculus)
- sec_multiaxis_refinement (refinement dynamics, support)
- sec_appendix (complexity bounds)

The remaining material is essentially identical. The introduction and conclusion have been lightly edited to remove references to the omitted material. The abstract is narrower and uses a different title ("Gluing Failure, Visible Quotients, and Pure-Ext Blind Spots" vs "Homological Visibility of Gluing Obstructions in a State-Forcing Semantics").

### V.2. Prior reviews

The sibling paper received two reviews:
1. **ChatGPT oracle (o3-mini-high):** REJECT, with 5 blockers and 7 medium issues.
2. **Claude Gate 3 review (P4_EDITORIAL_REVIEW_2026-04-03):** MINOR_REVISION.

The Claude review found that the ChatGPT REJECT was driven primarily by a false positive (B1: phantom unresolved references that did not actually exist in the sibling's compiled tex). The sibling paper's bibliography was complete.

### V.3. Issues from prior reviews that are resolved in this version

- The sibling review's recommendation to "tighten Section 5" (refinement dynamics) is addressed by removing that section entirely.
- The recommendation to cut the branch aggregation and complexity material is likewise addressed.
- The paper's scope is narrower and more focused, as recommended.

### V.4. Issues from prior reviews that REMAIN UNRESOLVED

1. **Undefinability qualification (M3 from oracle, item 1 from Claude):** The "In particular" clause in thm:pointwise-irreducibility is still overstated. Not fixed.
2. **UCT expansion (M6 from oracle, item 2 from Claude):** The compressed proof step in thm:intrinsic-visible-quotient is still compressed. Not fixed.
3. **$H_\alpha$ vs $K_\omega$ motivation (M5 from oracle, item 3 from Claude):** This is partially addressed by the focused version's removal of the strict visible quotient material, which eliminates the $H_\alpha$ concept entirely. The focused version only uses $K_\omega$, so the distinction no longer needs to be motivated. **Resolved by omission.**
4. **Cech-simplicial identification remark (item 5 from Claude):** Not added. Still relevant.
5. **Instantiate one conservative-extension pair (item 6 from Claude):** Not done.
6. **Contextuality comparison scope (item 7 from Claude):** The focused version retains the contextuality comparison theorem at the same level of conditionality. Not changed.

### V.5. NEW issues introduced by the focused narrowing

1. **BLOCKER: 7 missing bibliography entries.** The sibling paper had a complete bibliography with 15 entries. The focused version's `references.bib` retains only 9 entries, dropping 6 that are still cited. This is the single most damaging defect.
2. **Orphan files.** The focused version leaves 4 files in the directory that are not compiled but reference labels in each other. These would confuse reviewers.
3. **Build not re-run.** The PDF was generated without bibtex, so all citations show as "[?]".

---

## VI. Journal Fit Assessment (APAL)

**Subject fit: GOOD.** The paper sits at the intersection of forcing semantics (03B45, 03F55), sheaf-theoretic algebra (18F20), and categorical logic (03G30). APAL publishes in all these areas. The connection to team/inquisitive semantics and to sheaf-theoretic contextuality gives two additional hooks for the APAL audience.

**Technical level: APPROPRIATE.** The paper uses standard tools (sites, sheafification, stacks, gerbes, UCT) but in a novel combination. The proofs are accessible to algebraically literate logicians.

**Length: FINE.** The compiled PDF is 20 pages. With the focused scope, this is well within APAL norms.

**Bibliography quality (once fixed):** The 15-16 references are appropriate. The core sources (Mac Lane-Moerdijk, Giraud, Hatcher, Stacks Project, Abramsky-Brandenburger, Caru) are the right ones. One might add SGA 4 for sheafification, but Mac Lane-Moerdijk and Johnstone already suffice.

---

## VII. Issue Summary Table

| ID | Severity | Section | Description |
|----|----------|---------|-------------|
| B1 | BLOCKER | references.bib | 7 cited keys missing from bibliography; all citations in PDF show as "[?]" |
| B2 | BLOCKER | build system | PDF not properly compiled; 104 undefined-reference warnings; bibtex never run |
| B3 | MEDIUM | directory | 4 orphan .tex files not compiled but present in submission directory |
| B4 | MEDIUM | submission_checklist.md | Stale theorem numbers, false claim about absent files |
| M1 | MEDIUM | thm:pointwise-irreducibility | Undefinability conclusion overstated (Padoa method only) |
| M2 | MINOR | thm:intrinsic-visible-quotient proof | UCT isomorphism step compressed |
| M3 | MINOR | document structure | Section 4 contains all 3 main theorems in 8 subsections spanning 14 pages |
| M4 | MINOR | def:finite-nerve-presentation | Cech-simplicial identification stated without explicit justification remark |
| M5 | MINOR | thm:unique-branch-contextuality-comparison | Parts (i)-(iii) are restatements; could be corollary |
| M6 | MINOR | sec_introduction.tex line 35 | Roadmap paragraph does not mention gerbe/homological subsections explicitly |

---

## VIII. Verdict and Path Forward

**Decision: MAJOR_REVISION.**

The mathematical content is sound and, in isolation, would merit MINOR_REVISION (consistent with the sibling paper's assessment). However, the bibliographic and build defects (B1, B2) are disqualifying: they produce a PDF that is literally unreadable in its citation apparatus. These are not hard fixes -- adding 6 bib entries and re-running the build is a 30-minute task -- but until they are done, the paper cannot be submitted.

**Minimum required for re-assessment:**
1. Add the 6 missing bibliography entries to `references.bib`.
2. Rebuild with full `pdflatex -> bibtex -> pdflatex -> pdflatex` cycle.
3. Remove or sequester the 4 orphan .tex files.
4. Update the submission checklist.
5. Qualify the undefinability conclusion (M1).

**After these fixes, the paper should re-enter at Gate 3 for a second-pass review. If the build is clean and the bibliography is complete, the expected outcome is MINOR_REVISION or ACCEPT.**

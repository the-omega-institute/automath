# P4 Editorial Review -- Recursive Addressing via Prefix Sites, Local Sections, and Inverse Limits

**Date:** 2026-04-04
**Reviewer role:** Gate 3 independent editorial review (Claude Opus 4.6)
**Target journal:** Theory and Applications of Categories (TAC)
**Paper directory:** `D:/omega/automath/papers/publication/2026_recursive_addressing_prefix_sites_tac/`
**Prior stage notes:** None found (no P2/P3 notes, no JOURNAL_FIT.md, no TRACK_BOARD.md). Oracle review file exists but is empty/malformed.

---

## 1. Decision

**MAJOR_REVISION**

---

## 2. Main Mathematical Blockers

### BLOCKER-M1: Proposition 4.1 uniqueness claim is unjustified

**Location:** Proposition 4.1 (lines 268--290), specifically the "Moreover" clause (line 275) and its proof (lines 285--289).

**Problem:** The proposition claims that "at most one global section $s \in \mathscr{R}(a)$ can restrict to a given compatible family of local sections $s_i \in \mathscr{R}(b_i)$." The proof argues that if $s, t$ have identical restrictions to each $b_i$ then "the presheaf semantics treats them as the same global readout over $a$." This is not a proof -- it is an assertion that restates the claim. The presheaf $\mathscr{R}$ is a functor to **Set**; elements of $\mathscr{R}(a)$ are abstract set elements. The restriction maps $\rho_{a \leftarrow b_i}$ need not be injective, and there is no axiom requiring them to be. Two distinct elements $s, t \in \mathscr{R}(a)$ can perfectly well map to the same image under every restriction map. That would make $\mathscr{R}$ non-separated, which is fine for a presheaf. The claim is **false in general for presheaves** -- it holds only for separated presheaves. Either:
- (a) The paper must add an explicit separatedness hypothesis to Proposition 4.1, or
- (b) The uniqueness clause must be removed from 4.1 and relocated to Section 6 where separatedness is discussed.

This is a genuine mathematical error, not a presentation issue.

### BLOCKER-M2: Corollary 4.2 trichotomy is incomplete and mislabeled

**Location:** Corollary 4.2 (lines 292--310).

**Problem:** The corollary lists three failure modes but omits the fourth case announced in the introduction and in Theorem 6.2: non-separatedness (two distinct global sections restrict to the same local data). The introduction (lines 82--85) lists three internal failure modes: empty fiber, descent failure, and non-separatedness. But Corollary 4.2 lists: (1) address not admissible, (2) empty fiber, (3) descent failure. Non-separatedness has been replaced by "address not admissible," which is a trivially different phenomenon (not an address failure but an input error). This creates an inconsistency with the introduction's three-part classification and with Theorem 6.2's three-part classification (i)/(ii)/(iii). The trichotomy should be made consistent throughout the paper.

### BLOCKER-M3: Cech obstruction is set up for a scenario that the paper does not construct

**Location:** Definition 4.3 and Proposition 4.4 (lines 317--353).

**Problem:** The definition introduces transition data $g_{ij} \in A$ on overlaps of an abelian group $A$ and defines a Cech 2-cocycle $\alpha_{ijk} = g_{ij} g_{jk} g_{ik}^{-1}$. But the readout presheaf $\mathscr{R}$ is a functor to **Set**, not to $A$-torsors or principal bundles. The transition data $g_{ij}$ are introduced out of thin air -- there is no mechanism in the paper that produces them from $\mathscr{R}$. The phrase "together with transition data" (line 322) is doing all the heavy lifting without justification.

For the Cech obstruction to be meaningful, the paper needs either:
- (a) A torsor structure on the fibers $\mathscr{R}(b_i)$ (i.e., $\mathscr{R}$ should be a presheaf of $A$-torsors, not of sets), with the $g_{ij}$ arising from comparing local trivializations, or
- (b) An explicit construction showing how the abstract set-valued presheaf gives rise to transition data in some group $A$.

Without this bridge, the entire obstruction theory in Sections 4.2 and 5 floats above the actual mathematical setup.

### BLOCKER-M4: Theorem 5.3 "spectral definability" lacks a defined term

**Location:** Theorem 5.3 (lines 425--451).

**Problem:** The theorem states that "a character-based spectral readout descends to a well-defined global object if and only if the chosen character lies in $H_\alpha^\perp$." The term "character-based spectral readout" is never defined. It appears to refer to applying a character $\chi \in \widehat{A}$ to the transition data, but since the transition data are not derived from the presheaf (see BLOCKER-M3), this theorem inherits the same gap. Additionally, "spectral definability" in the theorem title is not defined anywhere in the paper.

### MEDIUM-M5: Proposition 5.1 and Theorem 5.2 are elementary algebra, not site theory

**Location:** Proposition 5.1 (lines 362--388), Theorem 5.2 (lines 390--423).

**Problem:** Proposition 5.1 says: the image of the generators of $H_\alpha$ in $A/H_\alpha$ is zero, and the quotient is universal. This is the definition of a quotient group. Theorem 5.2 says: if $A \hookrightarrow (A/H) \times R$, then $|R| \geq |H|$. This is a fiber-counting argument for any group surjection, completely independent of sites, presheaves, or addresses. Neither result uses any structure specific to the prefix site or to recursive addressing. These should be presented as what they are (elementary group-theoretic observations) rather than as theorems about the site, or the paper should explain concretely what $A$ and $H_\alpha$ are in the context of a specific recursive addressing scenario.

### MEDIUM-M6: Theorem 6.1 is a standard result, not attributed

**Location:** Theorem 6.1 (lines 457--552).

**Problem:** Parts (1) and (2) are the standard construction of the inverse limit of finite sets as a compact ultrametric space. Part (3) is the nested closed sets / Cantor intersection theorem applied to a complete metric space with diameter shrinking to zero. All three parts are textbook results (e.g., Bourbaki General Topology, or any introduction to profinite spaces). The paper presents these as if they are original theorems. TAC referees will immediately notice this. The paper should either: cite the standard source and state the theorem as a "Recall" or "For completeness we record...," or trim it to a proposition with a short proof sketch.

---

## 3. Editorial Blockers

### BLOCKER-E1: Paper does not use TAC document class or formatting

**Location:** Line 1 (`\documentclass[11pt,letterpaper]{article}`).

**Problem:** TAC has a specific document class (`tac.cls`) and formatting requirements. The paper uses generic `article.cls` with `letterpaper` and 1-inch margins. TAC uses its own layout. The author field is empty (line 36). For submission to TAC, the paper must use the TAC document class or at minimum follow TAC's formatting conventions. This is a hard editorial requirement.

### BLOCKER-E2: Bibliography is not compiled and contains only 4 textbook entries

**Location:** `references_local.bib` (4 entries), LaTeX log (undefined citation warnings).

**Problem:**
1. The bibliography was never compiled with BibTeX -- all citations appear as `[?]` in the PDF.
2. Four textbook references (Walters, Mac Lane-Moerdijk, Bredon, Munkres) are grossly insufficient for a TAC paper. There is zero engagement with the existing literature on:
   - Grothendieck topologies and sites (SGA4, Artin, Vistoli)
   - Prefix codes and symbolic dynamics (Lind-Marcus, Kitchens)
   - Cech cohomology on sites (Artin, Milne, Tamme)
   - Inverse limits of profinite spaces (Ribes-Zalesskii, Wilson)
   - Descent theory (Grothendieck FGA, Vistoli's notes)

   A TAC paper about sites with Cech obstruction theory that does not cite SGA4 or any of the standard descent references will be desk-rejected.

### BLOCKER-E3: No examples

**Problem:** The paper is entirely abstract. There is not a single concrete example of:
- A specific prefix site with specific addresses
- A specific readout presheaf with computed fibers
- A specific cover where the Cech obstruction is nontrivial
- A specific inverse system where Theorem 6.1 applies nontrivially

TAC publishes papers with substantial categorical content. A paper at this level of abstraction, with results that are either standard or elementary, needs worked examples to justify publication.

### MEDIUM-E4: Abstract mentions "abelian group" obstruction theory but the connection to the presheaf is never made

**Location:** Abstract (lines 42--58).

**Problem:** The abstract promises a "Cech-type class, the minimal visible quotient on which the obstruction vanishes, and a sharp register lower bound for recovering the full resolution." But the abelian group $A$ is introduced as a free parameter in Definition 4.3 without any derivation from the presheaf $\mathscr{R}$. The abstract implies these are consequences of the prefix site setup; in reality they are consequences of having an abelian group with a cocycle, which has nothing to do with the prefix site.

### MEDIUM-E5: "Master manuscript" references create unclear provenance

**Location:** Lines 71, 77, 101.

**Problem:** The paper refers to a "master manuscript" three times. For a standalone TAC submission, this is inappropriate. A published paper must be self-contained and not refer to unpublished companion documents as if the reader has access to them. Either cite a specific preprint (with arXiv number) or remove these references entirely.

### MINOR-E6: Cech should be written as \v{C}ech

**Location:** Throughout (lines 88, 102, 312, 314, 317, 326, 327, 332, 345).

**Problem:** "Cech" should be "\v{C}ech" everywhere. This is a standard typographical convention.

### MINOR-E7: Discussion section (Section 7) is thin

**Location:** Lines 616--640.

**Problem:** The discussion is less than one page and does not discuss: relation to existing work on sites in symbolic dynamics, limitations of the approach, open questions, or potential applications. For TAC, a more substantive discussion linking to the categorical literature is expected.

### MINOR-E8: Table 1 uses "master-paper phrase" as a column header

**Location:** Lines 107--122.

**Problem:** A standalone submission should not have a table translating terminology from an unpublished manuscript. If the table is kept, it should translate from commonly used informal terminology, not from a private document.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

| # | Location | Problem | Fix |
|---|----------|---------|-----|
| 1 | Prop 4.1, lines 275--289 | Uniqueness claim is false for general presheaves | Remove the "Moreover" clause, or add a separatedness hypothesis. If kept, prove injectivity of the restriction map to the product, do not assert it. |
| 2 | Cor 4.2, lines 292--310 | Trichotomy inconsistent with intro and Thm 6.2 | Align the three cases with the three announced in the intro: empty fiber, descent failure, non-separatedness. Remove "address not admissible" (it is a precondition, not a failure mode). |
| 3 | Def 4.3, lines 317--333 | Transition data $g_{ij}$ appear without derivation from $\mathscr{R}$ | Either upgrade $\mathscr{R}$ to a presheaf of $A$-torsors with explicit structure, or provide a concrete construction showing how $g_{ij}$ arises from comparing local sections. |
| 4 | Thm 5.3, lines 425--451 | "Character-based spectral readout" undefined | Define this term precisely before stating the theorem. Explain what object the character is applied to. |
| 5 | Prop 5.1 + Thm 5.2, lines 362--423 | Results are elementary algebra, presented as site-theoretic theorems | Downgrade to lemmas, state them as group-theoretic observations. Add a concrete example computing $H_\alpha$ for a specific prefix site. |
| 6 | Thm 6.1, lines 457--552 | Standard textbook result presented as original | Rewrite as "Theorem (Standard)" or "Proposition" with attribution. Shorten the proof to a sketch with reference. |
| 7 | Line 1 | Wrong document class | Use `tac.cls` or follow TAC formatting guidelines. |
| 8 | `references_local.bib` | Only 4 textbook references, no site/descent/symbolic dynamics literature | Add at minimum: SGA4, Vistoli descent notes, Johnstone Sketches of an Elephant or Stone Spaces, Lind-Marcus symbolic dynamics, standard Cech cohomology reference. Target 15-25 references. |
| 9 | All sections | No examples | Add at least two worked examples: (a) a binary prefix site with explicit cover and computed $\mathscr{R}$ fibers; (b) an example where $H_\alpha \neq 0$ and the register bound is achieved. |
| 10 | Lines 71, 77, 101 | "Master manuscript" references | Remove or replace with a specific arXiv citation. |
| 11 | Throughout | "Cech" not "\\v{C}ech" | Replace all instances with \v{C}ech. |
| 12 | Line 36 | Author field empty | Add author name(s). |
| 13 | Discussion (Sec 7) | Too thin, no literature engagement | Expand to discuss: relation to Johnstone's coverage theorem, comparison with standard Grothendieck descent, connections to symbolic dynamics coding theory, open questions. |

---

## 5. Comparison with Prior Stage Notes

No prior P2/P3 notes were found in the paper directory. The oracle review file (`oracle/done/recursive_addressing_prefix_review.md`) is malformed (contains only repeated "main" strings), indicating no usable prior review exists.

**This is the first substantive review of this paper.**

---

## 6. Novelty Assessment for TAC

The paper's claimed contributions are:

1. **Prefix site formalization of recursive addressing:** The construction of a site from prefix-ordered addresses is straightforward. The Grothendieck topology is generated by finite cylinder covers. This is a natural construction but not deep -- it is essentially the observation that prefix codes form a site, which is implicit in existing work on symbolic dynamics and Boolean algebras.

2. **Cech obstruction theory on the prefix site:** As noted in BLOCKER-M3, this is not actually derived from the prefix site; it is generic Cech cohomology of an abelian group-valued cocycle on any site. The paper does not demonstrate a phenomenon specific to prefix sites.

3. **Register lower bound (Theorem 5.2):** This is a fiber-counting argument for group quotients. It has nothing to do with sites.

4. **Dyadic inverse-limit theorem (Theorem 6.1):** This is the Cantor intersection theorem in a complete metric space with a profinite indexing. Standard.

5. **Separatedness criterion (Theorem 6.2):** The equivalence of (1) and (2) is essentially the definition of separatedness restated in the specific setting. The trichotomy (i)/(ii)/(iii) is the standard classification of sheaf-theoretic failure modes.

**Overall:** The paper reorganizes standard categorical and topological machinery (sites, presheaves, Cech cohomology, inverse limits, separatedness) around a specific motivating example (recursive addressing). The reorganization is competent but the mathematical content is not deep enough for TAC without: (a) a genuinely new theorem that requires the specific structure of prefix sites, or (b) substantial worked examples demonstrating that the framework reveals non-obvious phenomena. Currently neither is present.

---

## 7. Summary of Severity Ratings

### BLOCKERs (must fix before resubmission)
- **BLOCKER-M1:** Proposition 4.1 uniqueness claim is mathematically incorrect for general presheaves
- **BLOCKER-M3:** Cech obstruction lacks derivation from the presheaf; transition data are ad hoc
- **BLOCKER-E1:** Wrong document class for TAC
- **BLOCKER-E2:** Bibliography fatally inadequate (4 textbook refs, not compiled)
- **BLOCKER-E3:** No examples anywhere in the paper

### MEDIUM (significant but fixable)
- **BLOCKER-M2:** Trichotomy inconsistent across paper
- **BLOCKER-M4:** "Spectral definability" / "character-based spectral readout" undefined
- **MEDIUM-M5:** Elementary algebra presented as site-theoretic theorems
- **MEDIUM-M6:** Standard results presented as original
- **MEDIUM-E4:** Abstract overpromises relative to content
- **MEDIUM-E5:** "Master manuscript" references inappropriate for standalone paper

### MINOR (polish)
- **MINOR-E6:** Cech -> \v{C}ech throughout
- **MINOR-E7:** Discussion section too thin
- **MINOR-E8:** Table 1 references private document

---

## 8. Recommendation

**MAJOR_REVISION.** The paper cannot be submitted to TAC in its current form. The three hard mathematical blockers (M1, M3, M4) mean the core technical content from Section 4.2 through Section 5 is not correctly connected to the site-theoretic setup. The editorial blockers (wrong format, inadequate bibliography, no examples) are independently sufficient to guarantee desk rejection.

To reach MINOR_REVISION status, the paper needs:
1. Fix the mathematical error in Proposition 4.1 (add separatedness hypothesis or remove uniqueness claim).
2. Either upgrade the presheaf to torsors to justify the Cech obstruction, or remove Sections 4.2 and 5 and restructure as a shorter paper about prefix sites and separatedness only.
3. Add at least two substantial worked examples.
4. Expand the bibliography to 15+ relevant references including standard site/descent theory sources.
5. Use TAC formatting.
6. Remove all "master manuscript" references.

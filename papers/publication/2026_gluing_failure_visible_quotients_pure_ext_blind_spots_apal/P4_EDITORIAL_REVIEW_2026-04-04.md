# P4 Editorial Review -- 2026-04-04

**Manuscript:** Gluing Failure, Visible Quotients, and Pure-Ext Blind Spots
**Target journal:** Annals of Pure and Applied Logic (APAL)
**Review type:** Gate 3 independent editorial review (first review)
**Reviewer model:** Claude Opus 4.6

---

## 1. Decision

**MAJOR_REVISION**

---

## 2. Main Mathematical Blockers

### 2.1. BLOCKER -- Six missing bibliography entries break compilation

The following citation keys appear in the compiled (included) .tex files but are absent from `references.bib`:

| Key | Used in |
|-----|---------|
| `Hatcher2002` | sec_homological_visibility (6 occurrences) |
| `Weibel1994` | sec_homological_visibility |
| `DummitFoote2004` | sec_homological_visibility (2 occurrences) |
| `Giraud1971` | sec_gerbe_obstruction (2 occurrences) |
| `Johnstone2002` | sec_null_decomposition |
| `StacksProject` | sec_null_decomposition, sec_gerbe_obstruction (7+ occurrences) |

The paper cannot compile with bibtex. Every reference to the universal coefficient theorem, banded gerbe classification, Pontryagin duality, and the Stacks Project is broken. This is a hard compilation blocker.

**Fix:** Add the six missing bib entries to `references.bib`. All are standard references and the entries are straightforward.

### 2.2. BLOCKER -- Four orphaned .tex files never input in main.tex

The directory contains four substantial .tex files that are NOT `\input` in `main.tex`:

| File | Content | Lines |
|------|---------|-------|
| `sec_multiaxis_refinement.tex` | Refinement dynamics, axis support, branch visibility monotonicity | 260 |
| `sec_conservativity.tex` | Concrete realization, semantic fidelity | 94 |
| `sec_observer_spacetime.tex` | Observer fibers, spacetime localization, coupled states | 179 |
| `sec_appendix.tex` | Finite-state complexity upper bounds | 30 |

The problem is threefold:

(a) **The cover letter claims the paper "omits the multi-branch budget calculus, refinement dynamics, and complexity appendix"** and the submission checklist states "No refinement-dynamics or complexity appendix remains in the APAL-focused version." Yet the files remain in the directory, which will confuse any editor or copyeditor.

(b) **`sec_multiaxis_refinement.tex` contains `thm:branch-visibility-monotonicity` (Refinement monotonicity of branch visibility)** which has a substantive mathematical claim about how the visible quotient transforms under refinement. This result is arguably more interesting than some of what is currently included (e.g., the typed readout material), and its absence weakens the paper's contribution.

(c) **`sec_appendix.tex` references `\Cref{def:axis-support,def:axis-indispensability}` from `sec_multiaxis_refinement.tex`** -- these are only defined in the non-included file. If anyone tries to add the appendix back, it will break.

**Fix:** Either (i) delete the four files from the submission directory entirely, or (ii) decide which additional content to include and update `main.tex` accordingly. The current state -- files present but not compiled -- is not acceptable for submission.

### 2.3. MEDIUM -- Theorem 4.29 (pointwise irreducibility) proof relies on an informal automorphism argument

The proof of Theorem 4.29 constructs a model automorphism $\alpha$ that swaps $r_1^M$ and $r_2^M$ while preserving each realization $\rho \in R_p$. The claim that such an automorphism exists is stated by fiat: "Choose the $\mathrm{Form}_1$-reduct of $M$ so that there is an automorphism..." This is logically valid (it is a constructive existence argument), but:

- The "model" is entirely ad hoc. The signature $\Sigma$ has not been specified. The proof does not verify that the chosen $M$ actually satisfies the axioms of any particular theory.
- The phrase "which preserves each realization $\rho \in R_p$" needs unpacking. If $R_p$ is a set of valuations in $M$, an automorphism of $M$ does not preserve valuations -- it permutes them. What is meant is that the induced permutation of $\Val_M(\Gamma_p)$ maps $R_p$ to itself. This should be stated precisely.
- The restriction in (i) that $\varphi(x)$ "containing no occurrence of the distinguished constants $r_1, r_2$ other than the substituted variable" is syntactically awkward. $r_1$ and $r_2$ are reference terms, not constants in a first-order signature in the usual sense. The paper should clarify whether $r_1, r_2$ are in the signature or are interpreted terms.

**Fix:** (a) State precisely: "the underlying sort domains are $D_s^M = \{0, 1\}$ with $r_1^M = 0$, $r_2^M = 1$, and $\alpha$ is the swap automorphism." (b) Clarify that $\alpha$ acts on $R_p$ by fixing it setwise. (c) Clarify the syntactic status of $r_1, r_2$.

### 2.4. MEDIUM -- Theorem 4.35 (gerbe-null-semantics) contains an unjustified cofinal-family hypothesis

The final clause of Theorem 4.35 states: "If, in addition, the chosen cofinal family of gerbe-adapted covers computes derived cohomology in degree 2..." This is a nontrivial hypothesis that is never verified for any example. Neither the $S^2$-type nor the $\mathbb{R}P^2$-type example in Section 4.8 checks this condition. The paper should either:

(a) verify the hypothesis for the two worked examples (this is straightforward: for finite good covers of $S^2$ and finite triangulations of $\mathbb{R}P^2$, Cech and derived cohomology agree), or
(b) state explicitly that the examples work with Cech cohomology alone and note where the derived comparison is needed.

**Fix:** Add a one-sentence justification in each example, or add a remark after Theorem 4.35.

### 2.5. MEDIUM -- The "four-layer chain" is claimed but only two layers are substantively used

Section 2 (sec_preliminaries) defines a chain $\mathbb{L}_0 \preceq \mathbb{L}_1 \preceq \mathbb{L}_2 \preceq \mathbb{L}_3 \preceq \mathbb{L}_4$ and says $\mathbb{L}_3$ "adds structural absence and gluing-obstruction data" while $\mathbb{L}_4$ "adds refinement dynamics." But:

- $\mathbb{L}_0$ and $\mathbb{L}_1$ are defined in Section 3.
- $\mathbb{L}_2$ is the local-object layer of Section 4.
- $\mathbb{L}_3$ and $\mathbb{L}_4$ are never formally defined anywhere in the included files.

The paper therefore promises a four-layer chain but delivers only two layers ($\mathbb{L}_0/\mathbb{L}_1$ and $\mathbb{L}_2$). The $\mathbb{L}_3$ and $\mathbb{L}_4$ definitions are presumably in the non-included files. This creates a dangling forward reference.

**Fix:** Either (a) remove the mention of $\mathbb{L}_3$ and $\mathbb{L}_4$ from Section 2, calling it a "two-layer" or "three-layer" paper, or (b) include the definitions of $\mathbb{L}_3$ and $\mathbb{L}_4$ even if the detailed development is omitted.

### 2.6. MEDIUM -- Standing refinement hypothesis in Section 4 is never formally stated

Section 4 opens with: "Throughout the section we assume that refinement acts conservatively on the local structures: if $q \le p$, then admitted references, covers, and compatible local families at $q$ restrict functorially to those at $p$, and a visible value class already uniquely determined at $p$ is not split by further refinement."

This is used critically in the proof of Proposition 4.20 (typed-readout persistence). However:
- This is an assumption on the model, not on the formalism. It should be stated as a formal definition or hypothesis, not as prose at the start of a section.
- The non-splitting condition is strong: it says sheafification of $F_{p,s}$ commutes with refinement transitions. This deserves a name and a label.

**Fix:** Introduce a numbered definition or hypothesis for this standing assumption, and reference it explicitly in proofs that depend on it.

### 2.7. MINOR -- Theorem 4.39 proof: the claim that $\eta_{\mathbb{T}}$ is an isomorphism needs the full UCT exact sequence, not just injectivity

The proof correctly argues that $\operatorname{Ext}^1(H_1, \mathbb{T}) = 0$ because $\mathbb{T}$ is divisible. It then says "Thus $\eta_{\mathbb{T}}$ is an isomorphism by Definition 4.36." The reference should be to the UCT exact sequence itself (which is stated in Definition 4.36), not to the definition. The logic is: the UCT gives a short exact sequence, the left term vanishes, hence the right map is an isomorphism. This is correct but the reference is misleading.

**Fix:** Replace "by Definition 4.36" with "by the universal coefficient exact sequence stated in Definition 4.36."

---

## 3. Editorial Blockers

### 3.1. BLOCKER -- Abstract contains author-defined macros

The abstract uses the notation $\operatorname{coker}(\mathrm{ev}_{\omega})$, $H_2(N(\mathcal{U}), \mathbb{Z})$, and $\operatorname{Ext}$, which are all standard LaTeX. This is fine. However, the abstract also uses the term "\v{C}ech nerve" which renders correctly but is not plain ASCII -- the submission checklist says "Abstract contains no citations and no author-defined macros." This is actually satisfied. No blocker here on second inspection.

### 3.2. BLOCKER -- The paper compiles to 20 pages but contains no bibliography

Due to the six missing bib entries, the compiled PDF (main.pdf, 454 KB) will have unresolved citation markers throughout. The aux file confirms all citations are undefined. The paper is not submittable in this state.

**Fix:** Add the missing bib entries and recompile (pdflatex -> bibtex -> pdflatex -> pdflatex).

### 3.3. MEDIUM -- Section structure is flat: everything is Section 4 with subsections

The paper has sections 1 (Introduction), 2 (Preliminaries), 3 (Information States), 4 (Local Objects...), 5 (Conclusion). But Section 4 contains 9 subsections (4.1--4.9) running from page 5 to page 19. This is structurally unbalanced. For APAL, this is acceptable but not ideal. The gerbe obstruction material (4.7) and the homological visibility material (4.8--4.9) are conceptually distinct from the local objects / structural absence material (4.1--4.6). Promoting them to top-level sections would improve navigability.

**Fix:** Consider promoting subsections 4.7 and 4.8--4.9 to top-level sections (Sections 5 and 6, with Conclusion becoming Section 7).

### 3.4. MEDIUM -- Introduction road-map references non-existent sections

The introduction states: "Section [sec:gerbe-obstruction] gives the branch-gerbe semantics of gluing failure. Section [sec:homological-visibility] develops the intrinsic visible quotient..."

These labels resolve to subsections 4.7 and 4.8 respectively. In the compiled PDF, the Cref output will say "Subsection 4.7" and "Subsection 4.8" rather than "Section 5" etc. This is not wrong, but the introduction says "sections" while they are subsections. Either the introduction text should say "subsection" or (preferred) the sections should be promoted.

**Fix:** Align the introduction language with the actual document structure.

### 3.5. MEDIUM -- No \author{} block

The `\author{}` field in main.tex is empty. The submission checklist notes this ("Replace the empty `\author{}` block..."). For APAL, author information is required at submission unless under double-blind review, which APAL does not use.

**Fix:** Fill in author information before submission.

### 3.6. MINOR -- Cover letter mentions "complexity appendix" being omitted, but sec_appendix.tex is present

The cover letter says "The present version omits the multi-branch budget calculus, refinement dynamics, and complexity appendix in order to keep the main theorem package focused." But `sec_appendix.tex` is physically present in the directory. While it is not compiled, its presence contradicts the claim.

**Fix:** Remove the file from the submission directory or include it.

### 3.7. MINOR -- MSC codes

The MSC codes are 03B45 (modal logic), 03F55 (intuitionistic mathematics), 03G30 (categorical logic, topos), 18F20 (presheaves and sheaves). These are reasonable for APAL. However, 18G50 (homological algebra -- non-abelian) might also be appropriate given the gerbe content.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### R1. [BLOCKER] references.bib -- Add missing entries

**Location:** `references.bib`
**Problem:** Six cited works have no bib entry.
**Fix:** Add entries for Hatcher (Algebraic Topology, 2002), Weibel (Homological Algebra, 1994), Dummit-Foote (Abstract Algebra, 2004), Giraud (Cohomologie non abelienne, 1971), Johnstone (Sketches of an Elephant, 2002), and the Stacks Project. Standard bibliographic data is readily available.

### R2. [BLOCKER] Directory cleanup -- Remove or include orphaned .tex files

**Location:** `sec_multiaxis_refinement.tex`, `sec_conservativity.tex`, `sec_observer_spacetime.tex`, `sec_appendix.tex`
**Problem:** Files present in directory but not compiled; confusing for editor/copyeditor.
**Fix:** Delete from submission directory. If any content should be retained, add `\input{}` to `main.tex`.

### R3. [MEDIUM] sec_preliminaries.tex lines 86--100 -- Remove or justify $\mathbb{L}_3, \mathbb{L}_4$ forward references

**Location:** `sec_preliminaries.tex`, lines 86--100
**Problem:** $\mathbb{L}_3$ and $\mathbb{L}_4$ are described but never formally defined in the compiled paper.
**Fix:** Rewrite as a two-layer or three-layer chain: $\mathbb{L}_0 \preceq \mathbb{L}_1 \preceq \mathbb{L}_2$, where $\mathbb{L}_0$ is pointwise, $\mathbb{L}_1$ is information-state forcing, and $\mathbb{L}_2$ is the local-object enrichment. Mention that further layers (structural absence, refinement dynamics) can be added conservatively, but do not name or number them as definite parts of "the complete setting of the present paper."

### R4. [MEDIUM] sec_null_decomposition.tex line 5 -- Formalize the standing refinement hypothesis

**Location:** `sec_null_decomposition.tex`, lines 4--6
**Problem:** Critical assumption stated only in prose.
**Fix:** Introduce a numbered hypothesis/definition (e.g., Definition 4.X "Refinement-stable local object system") and reference it by label in Proposition 4.20 and anywhere else it is used.

### R5. [MEDIUM] sec_null_decomposition.tex, Theorem 4.29 proof -- Tighten the automorphism argument

**Location:** `sec_null_decomposition.tex`, lines 541--575
**Problem:** Model construction is informal; syntactic status of $r_1, r_2$ unclear; "preserves each realization" is imprecise.
**Fix:** Specify a concrete finite model (e.g., $D_s^M = \{0,1\}$), state that $\alpha$ fixes $R_p$ setwise, and clarify that $r_1, r_2$ are constants in the expanded signature.

### R6. [MEDIUM] sec_gerbe_obstruction.tex + sec_homological_visibility.tex -- Verify cofinal-family hypothesis in examples

**Location:** Examples 4.47 and 4.48 in `sec_homological_visibility.tex`
**Problem:** The examples use the final clause of Theorem 4.35 without verifying its cofinal-family hypothesis.
**Fix:** Add one sentence to each example noting that for finite good covers of $S^2$ (resp. finite triangulations of $\mathbb{R}P^2$), Cech cohomology agrees with derived cohomology, so the hypothesis is satisfied.

### R7. [MEDIUM] Overall structure -- Promote subsections to sections

**Location:** `main.tex`, `sec_gerbe_obstruction.tex`, `sec_homological_visibility.tex`
**Problem:** Section 4 is disproportionately long (15 pages, 9 subsections).
**Fix:** Promote sec_gerbe_obstruction (currently 4.7) to Section 5, sec_homological_visibility (currently 4.8--4.9) to Section 6, and Conclusion to Section 7. Change `\subsection` to `\section` in the two files and update the introduction's road-map.

### R8. [MINOR] sec_homological_visibility.tex line 97 -- Fix reference target in proof

**Location:** `sec_homological_visibility.tex`, line 97
**Problem:** "by Definition 4.36" should be "by the universal coefficient exact sequence (Definition 4.36)."
**Fix:** Reword as suggested.

### R9. [MINOR] Bibliography scope -- Consider additional references

**Location:** `references.bib`
**Problem:** The bibliography is thin (currently 8 entries in bib, should be ~14 after fixes). For a paper touching team semantics, sheaf theory, gerbes, contextuality, and homological algebra, the reference list is narrow. Missing from the conversation:
- V\"a\"an\"anen (Dependence Logic, 2007) -- foundational for team semantics.
- Abramsky et al. (Contextuality, Cohomology and Paradox, 2015) -- the cohomological refinement.
- Brion (Gerbes on classifying stacks, etc.) or Breen (On the classification of 2-gerbes) -- standard gerbe references.
**Fix:** Add 3--5 additional standard references to demonstrate awareness of the relevant literature.

---

## 5. Comparison with Prior Stage Notes

### 5.1. Review notes (review_notes.txt, dated 2026-03-23)

The review_notes document 8 revision points. Status:

| # | Issue | Status |
|---|-------|--------|
| 1 | Theorem 4.26 correctness (unconditional decomposition) | **RESOLVED** -- now Corollary 4.33 under branch constancy. |
| 2 | Theorem 4.28 (gerbe-null-semantics) missing justification | **RESOLVED** -- global conservativity (Def 4.12) and Prop 4.13 added. |
| 3 | Forcing necessity theorem needed | **RESOLVED** -- Theorem 4.29 added. (But proof needs tightening; see 2.3 above.) |
| 4 | Connection to contextuality | **RESOLVED** -- Theorem 4.49 and Remark 4.50 added. |
| 5 | Remove "larger architecture" language | **RESOLVED** -- no traces found. |
| 6 | Complexity to appendix | **PARTIALLY RESOLVED** -- file exists as sec_appendix.tex but is NOT input in main.tex. The appendix is effectively removed but the file lingers. |
| 7 | Split large file | **RESOLVED** -- sec_null_decomposition split into three files. |
| 8 | Update abstract/intro/conclusion | **RESOLVED** -- all updated. |

### 5.2. New issues introduced by revision

1. The bibliography was not updated to include the references needed by the new homological-visibility section (Hatcher, Weibel, Dummit-Foote, Giraud, Johnstone, Stacks Project). This is the main new blocker.
2. The orphaned .tex files (multiaxis, conservativity, observer-spacetime, appendix) create confusion about what is and is not part of the paper.
3. The $\mathbb{L}_3/\mathbb{L}_4$ forward reference in sec_preliminaries is a residue from the longer manuscript that was not cleaned up.

---

## 6. APAL Fit Assessment

**Scope:** The paper sits at the intersection of information-state semantics (team/inquisitive logic), sheaf theory on sites, and cohomological obstruction theory. All three are within APAL's scope. The connection to sheaf-theoretic contextuality (Abramsky-Brandenburger) is relevant given recent APAL publications by Albert-Gradel (2022) and Ciardelli-Grilletti (2022).

**Novelty:** The main genuinely new result is the identification of the intrinsic visible quotient $A_{\mathrm{vis}}^{\omega} = \operatorname{coker}(\mathrm{ev}_{\omega})$ and the characterization of character-blind obstructions as pure Ext-type. This is a clean, nontrivial observation. The forcing-necessity theorem (Theorem 4.29) is straightforward but useful. The branch-gerbe semantics (Section 4.7) is a competent application of standard stack/gerbe theory to the information-state setting. Overall novelty is moderate -- the paper applies known algebraic machinery in a new logical context rather than developing fundamentally new techniques.

**Depth:** The homological results (Section 4.8) are the deepest part. The universal-coefficient decomposition is standard, but its semantic interpretation as visible/blind decomposition is new. The rest is definitional development of moderate depth.

**Writing quality:** High. The paper is clearly written, definitions are precise, proofs are complete (modulo the issues flagged above), and the exposition is systematic. The avoidance of hand-waving is notable.

**Length:** At 20 pages (compiled), the paper is appropriate for APAL.

**Overall APAL fit:** Good, contingent on fixing the blockers.

---

## 7. Summary of Issues by Severity

### BLOCKER (must fix before submission)
1. Six missing bibliography entries (R1)
2. Four orphaned .tex files in directory (R2)

### MEDIUM (should fix before submission)
3. $\mathbb{L}_3/\mathbb{L}_4$ forward references to undefined layers (R3)
4. Standing refinement hypothesis not formalized (R4)
5. Theorem 4.29 proof needs tightening (R5)
6. Cofinal-family hypothesis unverified in examples (R6)
7. Structural imbalance: Section 4 too long (R7)
8. Empty \author{} block (3.5)
9. Introduction road-map says "section" for subsections (3.4)

### MINOR (nice to fix)
10. Proof reference wording in Theorem 4.39 (R8)
11. Thin bibliography (R9)
12. Cover letter / directory inconsistency (3.6)
13. Possible additional MSC code (3.7)

---

**Verdict: MAJOR_REVISION.** The paper has genuine mathematical content and is well-written, but cannot be submitted with a broken bibliography. The orphaned files, undefined layer references, and structural issues require coordinated attention. After fixing the two blockers and addressing the medium issues, the paper should be ready for a MINOR_REVISION or ACCEPT assessment.

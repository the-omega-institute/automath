# P4 Editorial Review -- 2026-04-04

**Paper:** A Discrete Stokes Formula for Fold-Truncation Defects Across Resolutions
**File:** `main.tex` (single file, 703 lines, ~8 compiled pages)
**Target journal:** Not specified in manuscript. Assessed for a mid-to-strong dynamical systems / combinatorics journal (e.g., *Ergodic Theory and Dynamical Systems*, *Israel Journal of Mathematics*, *Journal of Combinatorial Theory Series A*).

---

## 1. Decision

**MAJOR_REVISION**

---

## 2. Main Mathematical Blockers

### 2.1 Theorems are correctly stated; proofs are complete for the deterministic core (Sections 2--6)

The Stokes identity (Theorem 4.1) is the main result. The proof via the telescoping auxiliary sequence $\Delta_j = A_j \oplus B_j$ is clean and complete. I verified the identity computationally for all binary words of length up to 6 with target lengths 1, 2, and 3, finding zero failures. The key algebraic step -- inserting $\pi(A_j)$ as a pivot in the XOR cancellation -- is correct since every element of $(\mathbb{Z}/2\mathbb{Z})^m$ is its own inverse.

The cocycle identity (Proposition 5.2) follows by splitting the Stokes sum at an intermediate scale. I verified this computationally as well (n=5,6 with various k,m). Correct.

The consistent-lift proposition (Proposition 6.1) is elementary: a summable sequence of nonneg integers has only finitely many nonzero terms. No issues.

Corollaries 4.2 and 5.1 are standard consequences (union bound, Lipschitz bound, subadditivity of Hamming weight). Correct.

### 2.2 Theorem 7.1 (Haar mixing): proof relies on unverified hypotheses and an unpublished reference

**BLOCKER.** The mixing theorem (Theorem 7.1) is the only result in the paper that is not self-contained. Two structural issues:

(a) **Assumptions (i) and (ii) are never verified for any specific $m$.** The paper assumes a finite-state realization and a character nondegeneracy condition but never demonstrates that these hold for the fold defect process. The theorem is therefore conditional in a strong sense: it is a general fact about additive functionals of hidden Markov chains applied to a setting where the hypotheses are merely asserted. For a journal submission, at least one of the following is needed:
- A proof or computational verification that (i) and (ii) hold for specific $m$ (even $m=1$ or $m=2$).
- An explicit construction of the finite-state machine and its transition matrices for a concrete case.
- A clear statement that this is a conditional result, with the hypotheses marked as conjectural for the fold setting.

(b) **The proof defers to an unpublished internal reference** (`Internal2026FoldGeneralizedStokesDefectHaarMixing`). The phrase "A detailed audit of the twisted-operator construction for the present Fold setting is recorded in [Internal2026...]" effectively outsources the most delicate part of the argument. A referee cannot accept this.

### 2.3 Novelty assessment

The discrete Stokes identity itself (Theorem 4.1) is a clean, exact telescoping formula for the failure of a natural diagram to commute. This is a genuinely new observation in the context of Zeckendorf normalization / Fibonacci numeration systems. No prior work that I am aware of formulates this specific defect or proves this identity.

However, the *technique* is not deep: it is a standard telescoping argument in a product of $\mathbb{Z}/2\mathbb{Z}$ groups. The "Stokes" analogy, while evocative, may overstate the depth. The result is closer to a discrete coboundary identity in a cochain complex than to a Stokes theorem in differential geometry. The paper should be more honest about this.

The corollaries (Sections 4.2, 5) are elementary consequences of the identity. The consistent-lift result (Section 6) is a trivial application of summability. The mixing theorem (Section 7) would be substantive if the hypotheses were verified, but as stated it is a conditional application of known Markov chain theory.

**Overall novelty: moderate.** The central identity is new and nontrivial, but the paper needs more substance to justify a standalone publication in a strong journal.

---

## 3. Editorial Blockers

### 3.1 Abstract vs. content mismatch

The abstract promises "auditable probability bounds, a Hamming--Lipschitz budget, and a cocycle formula across intermediate scales" and "exponential mixing to Haar measure." The deterministic results deliver on the first promise. The mixing result does not deliver because assumptions (i) and (ii) are never verified. The abstract should state explicitly that the mixing result is conditional.

### 3.2 Missing author

Line 34: `\author{}` is blank. Must be filled before submission.

### 3.3 Bibliography is completely broken

All 4 citations are undefined. The `.bib` files referenced on line 701 point to a sibling directory (`2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/`) that does not exist in the paper's directory tree. The compiled PDF has no bibliography section at all -- every citation renders as `[?]`.

This is a hard blocker. The paper cites:
- `Zeckendorf1972` -- standard, must be present
- `WaltersErgodicTheory` -- standard reference, must be present
- `LevinPeresWilmer2009MarkovMixing` -- standard Markov chain mixing reference, must be present
- `Internal2026FoldGeneralizedStokesDefectHaarMixing` -- unpublished internal document; cannot be cited in a journal submission without being publicly accessible

### 3.4 The bibliography is too thin

Four references total (one of which is unpublished) is insufficient for any journal. Missing references that should be cited:

- Lekkerkerker (1952) or Day (1969) for Zeckendorf-type representations
- Fraenkel (1985) or other work on Fibonacci numeration systems
- Berstel/Reutenauer on numeration systems and automata
- Relevant work on golden-mean shifts (Lind/Marcus textbook at minimum)
- The ergodic theory / symbolic dynamics literature on factor maps and resolution (e.g., Boyle, Kitchens, Marcus)
- If the "Stokes" analogy is to be maintained, at least a brief discussion of discrete Stokes theorems in combinatorics (e.g., Forman's discrete Morse theory, or simplicial cohomology)

### 3.5 Introduction is adequate but undersells context

The introduction correctly states the problem and the main results. However, it does not position the work within the existing literature on:
- Fibonacci numeration and normalization (there is a substantial literature)
- Multiscale analysis in symbolic dynamics
- Cohomological obstructions in dynamics

Without this context, a reader cannot assess whether the result is new or a reformulation of known facts.

### 3.6 No comparison with prior work

The paper states "We use only the minimal background on Zeckendorf normalization and symbolic systems" but never explains what is known and what is new. A "Related Work" or "Comparison" paragraph is needed.

### 3.7 Cross-references compile but with warnings

All internal cross-references (`\ref`) are correctly placed and would resolve after a second LaTeX pass. No dangling references.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### BLOCKER-1: Fix bibliography
- **Location:** Line 700-701 (`\bibliography{...}`)
- **Problem:** Bibliography files do not exist at the referenced path. All citations render as `[?]`.
- **Fix:** Create a local `.bib` file in the paper directory with all 4 references (3 real + remove or replace the internal one). Add at least 8-10 additional references to properly contextualize the work.

### BLOCKER-2: Verify or weaken Theorem 7.1 hypotheses
- **Location:** Section 7.1, Theorem 7.1, lines 570-627
- **Problem:** Assumptions (i) and (ii) are never verified. The proof cites an unpublished internal document.
- **Fix:** Either (a) construct the finite-state machine explicitly for $m=1$ or $m=2$ and verify both assumptions, turning this into a proved theorem for those cases, or (b) clearly label this as a conditional result ("Theorem 7.1 (conditional)") and remove the internal citation, replacing it with a self-contained proof sketch of why the twisted transfer operator spectral gap follows from (i)+(ii).

### BLOCKER-3: Fill in author field
- **Location:** Line 34
- **Problem:** `\author{}` is blank.
- **Fix:** Add author name(s) and affiliation(s).

### MEDIUM-1: Expand introduction with related work
- **Location:** Section 1 (Introduction), lines 61-108
- **Problem:** No positioning against existing literature on Fibonacci numeration, symbolic dynamics factor maps, or discrete cohomology.
- **Fix:** Add 1-2 paragraphs after the current introduction summarizing: (a) the state of the art in Zeckendorf normalization, (b) what is known about resolution towers in symbolic dynamics, (c) why this defect has not been previously studied.

### MEDIUM-2: Justify the "Stokes" terminology
- **Location:** Title, abstract, Theorem 4.1 label
- **Problem:** The identity $D = \bigoplus \pi(\kappa)$ is a telescoping sum / cocoboundary, not a Stokes theorem in any standard differential-geometric sense. Using "Stokes" may raise referee eyebrows.
- **Fix:** Add a remark after Theorem 4.1 explicitly explaining the analogy: the local defects play the role of "curvature" and the identity relates a "boundary integral" (global defect) to an "interior sum" (local curvatures). Acknowledge that this is an analogy, not a formal instance of the Stokes theorem.

### MEDIUM-3: Add computational examples for the Stokes identity
- **Location:** After Theorem 4.1 or in a new subsection
- **Problem:** The paper has only one example (Example 2.2) showing non-commutation. There is no worked example of the Stokes identity itself.
- **Fix:** Add an example with $n=3$, $m=1$ (or $n=4$, $m=2$) showing both sides of the Stokes formula evaluated on a specific word. This is crucial for readability.

### MEDIUM-4: The $\delta_m$ in Proposition 6.1 is not the same as $\kappa$
- **Location:** Section 6.1, Proposition 6.1, lines 520-553
- **Problem:** Proposition 6.1 defines $\delta_m = x_m \oplus \pi_{m+1\to m}(x_{m+1})$ where $x_m = \text{Fold}_m(r_{\infty\to m}(\omega^\infty))$. This is the same as $\kappa_{m+1\to m}(r_{\infty\to m+1}(\omega^\infty))$ by Definition 3.1, but the paper does not make this connection explicit.
- **Fix:** Add one sentence: "Note that $\delta_m = \kappa_{m+1\to m}(r_{\infty\to m+1}(\omega^\infty))$, so the summability condition is exactly the summability of adjacent local defects along the Fold trajectory of $\omega^\infty$."

### MEDIUM-5: The "curvature" terminology is unexplained
- **Location:** Definition 3.1, line 210 ("Local Curvature Defect")
- **Problem:** The defect is called "curvature" but no geometric interpretation is given.
- **Fix:** Either justify the terminology (e.g., by analogy with discrete curvature in graph theory or lattice gauge theory) or drop it and just call it "local defect."

### MINOR-1: Notation $|\cdot|_0$ not defined before use
- **Location:** Line 261, Table 1
- **Problem:** The Hamming weight notation $|v|_0$ is used in Table 1 and throughout but never formally defined.
- **Fix:** Add a line in Section 3 or 2: "For $v \in \{0,1\}^m$, let $|v|_0 := \#\{i : v_i \neq 0\}$ denote the Hamming weight."

### MINOR-2: Variable clash in Theorem 7.1
- **Location:** Lines 594, 600
- **Problem:** The contraction rate is called $\eta_m$ (line 594) but $\eta$ also appears as a generic element of $\Omega_{m+1}$ throughout the paper (e.g., Definition 3.1 line 212). This is a collision.
- **Fix:** Rename the contraction rate to $\rho_m$ or $\lambda_m$.

### MINOR-3: Inconsistent use of $\pi$ for two different maps
- **Location:** Lines 129, 143-146
- **Problem:** $\pi_m$ in line 129 truncates an infinite sequence to length $m$, while $\pi_{n\to m}$ in line 143 restricts a finite admissible word. The relationship between $\pi_m$ and $\pi_{\infty \to m}$ (introduced later in Section 6) is never clarified.
- **Fix:** Unify notation. Either use $\pi_{\infty \to m}$ from the start in Definition 2.1, or add a remark clarifying that $\pi_m$ in the Fold definition is the same as $\pi_{\infty \to m}$ restricted to the relevant digits.

### MINOR-4: Spacing issue in Corollary 4.2 proof
- **Location:** Line 396
- **Problem:** "Theorem \n~\ref{thm:...}" has a linebreak before the tilde, which may produce a visible space in output.
- **Fix:** Remove the newline: `Theorem~\ref{thm:fold-discrete-stokes-defect}`.

### MINOR-5: No `\date` should be set for submission
- **Location:** Line 35
- **Problem:** `\date{\today}` will print the compilation date, not a fixed date.
- **Fix:** Either remove `\date` or set it to a specific date for the submission version.

---

## 5. Comparison with Prior Stage Notes

No P2/P3 notes exist for this paper. This is the first editorial review.

---

## 6. Summary Assessment

### Strengths
- The core identity (Theorem 4.1) is clean, correct, and verified computationally.
- The paper is well-scoped: it isolates one precise phenomenon and proves it rigorously.
- The proof structure is clear and the writing is generally good.
- The deterministic results (Sections 2-6) are self-contained and complete.

### Weaknesses
- The bibliography is completely broken (hard blocker for submission).
- Theorem 7.1 is conditional on unverified hypotheses and cites an unpublished source.
- The paper is thin on context: no related work, minimal references.
- The novelty of the core result, while real, is modest -- it is a telescoping identity in $(\mathbb{Z}/2\mathbb{Z})^m$. The paper needs to work harder to explain why this matters.
- No computational data beyond one 2-bit example.

### Journal Fit
In its current state, the paper is not ready for a strong journal. After revisions:
- With Theorem 7.1 verified and substantial context added: suitable for *Ergodic Theory and Dynamical Systems* or *Israel J. Math.*
- With the conditional result clearly marked and context added: suitable for *Discrete Mathematics*, *Journal of Integer Sequences*, or *Integers*.
- The paper could also work as a short note in *Proceedings of the AMS* if tightened to ~5 pages focusing on the Stokes identity alone.

---

## Top 3 Blockers for TRACK_BOARD

1. **BLOCKER-1:** Bibliography files missing; all citations render as `[?]`. No bibliography in compiled PDF.
2. **BLOCKER-2:** Theorem 7.1 hypotheses (i) and (ii) never verified; proof cites unpublished internal document.
3. **BLOCKER-3:** Author field is blank.

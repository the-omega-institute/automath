# P4 Editorial Review -- 2026-04-04

**Paper:** Optimal Cubical Poincare--Stokes Inverses and Boundary Readout on Dyadic Approximations

**Target Journal:** JDSGT (Journal of Differential Geometry and Topology) or similar strong geometry/topology journal (e.g. Advances in Mathematics, Geometriae Dedicata)

**Reviewer:** Gate 3 independent editorial review (first pass)

---

## 1. Decision

**REJECT**

The main theorem (Theorem 3.1, sharp bound $1/(2k)$) has a concrete counterexample for the coefficient sup norm used in the paper. See BLOCKER-1 below. Every downstream result inherits this error. The paper must return to P2 (mathematical development) to either fix the norm, fix the bound, or restructure the results for decomposable forms only.

---

## 2. Main Mathematical Blockers

### BLOCKER-1: Contraction estimate (Lemma 2.1) is incomplete for general k-forms

**Location:** Lines 190--203 (Lemma 2.1 and its proof)

**Problem:** The proof claims "contracting a coefficient form by X multiplies each coefficient by one of these components." This is imprecise and, in the stated generality, not obviously correct. For a general k-form $\omega = \sum_{|I|=k} a_I(x) dx_I$, the interior product $\iota_X \omega$ produces a (k-1)-form whose coefficients are *linear combinations* of the $a_I$ weighted by the components $X^j = x_j - 1/2$. Specifically:

$$(\iota_X \omega)_J = \sum_{j \notin J} \pm (x_j - 1/2) a_{\{j\} \cup J}(x).$$

Each such coefficient is a sum of up to $(n - k + 1)$ terms, each bounded by $(1/2) \|omega\|_\infty$. The naive bound therefore gives $\|\iota_X \omega\|_\infty \le \frac{n-k+1}{2} \|\omega\|_\infty$, not $\frac{1}{2}\|\omega\|_\infty$.

**However**, looking more carefully: the coefficient sup norm as defined on line 159 takes the max over multi-indices. For a fixed multi-index $J$ with $|J| = k-1$, the coefficient $(\iota_X \omega)_J$ involves a sum over those $j$ such that $\{j\} \cup J$ is an increasing sequence of length $k$. Each term is $\pm (x_j - 1/2) a_{\{j\}\cup J}$, and indeed there can be multiple terms.

The claim $\|\iota_X \omega\|_\infty \le \frac{1}{2}\|\omega\|_\infty$ holds only if we interpret the contraction component-by-component in a specific way. The proof needs to explicitly address why the *sum* of multiple terms does not blow up. As stated, the one-sentence argument is wrong for k-forms with $k \ge 2$ unless additional cancellation or a refined norm argument is given.

**Severity:** This is a hard blocker. If the contraction estimate fails, the sharp constant $1/(2k)$ in Theorem 3.1 is incorrect, and the entire paper collapses.

**Fix:** Either (a) prove the estimate properly by working out $\iota_X \omega$ component by component and showing that for each output coefficient, only one input coefficient contributes (which would require careful index bookkeeping), or (b) if the estimate is indeed wrong, restate with the correct constant. The key question is: for a fixed $(k-1)$-multi-index $J$, how many values of $j$ contribute to $(\iota_X \omega)_J$? If exactly one, the lemma is correct but the proof must say so explicitly; if more than one, the lemma is false.

**Resolution note:** On further reflection, for $J = (j_1, \ldots, j_{k-1})$ sorted, the contributing indices $j$ are precisely those such that inserting $j$ into $J$ gives a sorted $k$-tuple. There can be up to $k$ such values (one for each gap in $J$). So the naive bound gives a factor of $k/2$, not $1/2$. This would make the sharp constant $1/2$ rather than $1/(2k)$. **This needs to be resolved before any other review matters.**

**UPDATE after careful re-examination:** Actually, the formula for interior product with the *coordinate* vector field $\partial/\partial x_j$ extracts the single coefficient $a_I$ where $j$ is the first element of $I$. But $X = \sum_j (x_j - 1/2) \partial/\partial x_j$ is a linear combination. So:

$$\iota_X \omega = \sum_j (x_j - 1/2) \iota_{\partial/\partial x_j} \omega.$$

For a fixed output multi-index $J$, $(\iota_{\partial/\partial x_j} \omega)_J = \pm a_{\{j\}\cup J}$ when $j \notin J$ and $0$ when $j \in J$. So multiple $j$-values contribute. The number of contributing terms for a given $J$ is $(n - k + 1)$, which can be as large as $n - 1$.

**Conclusion:** The Lemma as stated appears to be **false** for $k \ge 2$ with this coefficient sup norm. The bound should be $\|\iota_X \omega\|_\infty \le \frac{n-k+1}{2}\|\omega\|_\infty$ in general. This is a fatal flaw.

**Concrete counterexample confirming the lemma is false.** Take $n = 3$, $k = 2$, and $\omega = dx_1 \wedge dx_3 + dx_2 \wedge dx_3$ on $I^3$. Then $\|\omega\|_\infty = 1$. Computing:

$$\iota_X \omega = (x_1 - 1/2)dx_3 - (x_3 - 1/2)dx_1 + (x_2 - 1/2)dx_3 - (x_3 - 1/2)dx_2.$$

The coefficient of $dx_3$ is $(x_1 - 1/2) + (x_2 - 1/2)$. At $(x_1, x_2) = (1, 1)$ this equals $1$. So $\|\iota_X \omega\|_\infty \ge 1 > \frac{1}{2} = \frac{1}{2}\|\omega\|_\infty$.

The lemma is false. The issue is that for a $(k-1)$-multi-index $J$, the coefficient $(\iota_X \omega)_J = \sum_{j \notin J} \pm(x_j - 1/2) a_{J \cup \{j\}}$ can involve multiple nonzero terms that add constructively.

**Note:** For *decomposable* forms (single wedge products like $dx_1 \wedge dx_2$), the lemma holds -- the counterexample requires $\omega$ to have multiple nonzero coefficients sharing an output index after contraction.

**This counterexample also breaks Theorem 3.1 (the main theorem).** For the same $\omega = dx_1 \wedge dx_3 + dx_2 \wedge dx_3$ on $I^3$, direct computation gives:

- Coefficient of $dx_3$ in $K_2\omega$ at $x$: $\frac{1}{3}[(x_1 - 1/2) + (x_2 - 1/2)]$, which equals $1/3$ at $(1,1,\cdot)$.
- Coefficient of $dx_1$ in $K_2\omega$ at $x$: $-\frac{1}{3}(x_3 - 1/2)$, max $= 1/6$.
- Coefficient of $dx_2$ in $K_2\omega$ at $x$: $-\frac{1}{3}(x_3 - 1/2)$, max $= 1/6$.

Therefore $\|K_2\omega\|_\infty = 1/3$, while $\frac{1}{2k}\|\omega\|_\infty = \frac{1}{4} \cdot 1 = 1/4$. Since $1/3 > 1/4$, the bound (3.2) is violated. The main theorem is false as stated.

The correct bound for $K_k$ with this coefficient sup norm appears to involve a factor depending on $\min(k, n-k+1)$ (the maximum number of terms in the interior product sum for a single output coefficient). The paper's claim that the constant is "dimension-free" is incorrect.

### BLOCKER-2: Sharpness argument in Theorem 3.2 has a logical gap

**Location:** Lines 366--381

**Problem:** The sharpness proof sets $\omega_0 := K_{k+1}\nu_0$ and claims $d\omega_0 = \nu_0$. But the homotopy formula gives $\omega_0 = K_{k+1}\nu_0$ implies $d(K_{k+1}\nu_0) + K_{k+2}(d\nu_0) = \nu_0$. Since $\nu_0$ is constant, $d\nu_0 = 0$, so $d(K_{k+1}\nu_0) = \nu_0$. OK, this checks out. Then the proof says: for any decomposition $\omega_0 = d\phi + \tilde{E}$ with $\tilde{E}$ determined only by $d\omega_0 = \nu_0$, we have $d\tilde{E} = \nu_0$. But this requires that $\tilde{E}$ depends only on $d\omega_0$, which is an assumption about the decomposition scheme, not about a particular form. The argument should be made more explicit: it needs to say that the map $d\omega \mapsto \tilde{E}$ is a right inverse to $d$ on $(k+1)$-forms, and then the Theorem 3.1 sharpness applies to that right inverse.

**Severity:** Medium. The argument is essentially correct but the logical structure is sloppy.

### BLOCKER-3: Discrete transfer proof (Theorem 4.1) -- homotopy identity on cochains not justified

**Location:** Lines 448--508

**Problem:** The proof defines $\mathcal{H}_{k+1} := \mathcal{I} \circ K_{k+1} \circ W$ and claims the identity $d\mathcal{H}_{k+1} + \mathcal{H}_{k+2}d = \mathrm{Id}$ on $C^{k+1}$. This is stated but not proved. The derivation should be:

$$d(\mathcal{I} K_{k+1} W) + (\mathcal{I} K_{k+2} W) d = \mathcal{I} d K_{k+1} W + \mathcal{I} K_{k+2} d W = \mathcal{I}(dK_{k+1} + K_{k+2}d)W = \mathcal{I} \cdot \mathrm{Id} \cdot W = \mathcal{I} W = \mathrm{Id}.$$

This uses $\mathcal{I} d = d \mathcal{I}$ and $dW = Wd$ (the chain map properties from Section 2.2). The proof should show these steps. More importantly, the identity $dK_{k+1} + K_{k+2}d = \mathrm{Id}$ holds on smooth forms (Theorem 3.1), but here it is applied to $W(\cdot)$ which are Whitney forms. The homotopy identity from Theorem 3.1 is stated for $\Omega^k_{\mathrm{sm}}(I^n)$, and one needs $W(C^{k+1}) \subset \Omega^{k+1}_{\mathrm{sm}}(I^n)$. Whitney forms are piecewise polynomial, not necessarily smooth on all of $I^n$. This regularity gap needs to be addressed.

**Severity:** Medium-to-high. The result is likely true but the proof has a regularity assumption that is not verified.

### BLOCKER-4: Cheeger--Stokes duality (Proposition 5.1) -- hypotheses are too strong to be useful

**Location:** Lines 592--662

**Problem:** The proposition assumes the existence of a calibrating vector field $V_*$ satisfying three conditions simultaneously. This is essentially assuming the conclusion in a disguised form. In particular, the condition $\|V_*\|_\infty \le h(\Omega)^{-1}$ together with $\mathrm{div}\, V_* = 1$ already implies $\mathcal{C}_\infty(\Omega) \le h(\Omega)^{-1}$. The other direction ($\ge$) follows from the divergence theorem alone and does not need the calibrating field. So the "duality principle" reduces to: if you can find a field achieving the bound, then equality holds. This is tautological.

The interesting mathematical content would be to *prove* the existence of such a calibrating field (at least for the cube), or to show the duality without assuming the calibrator. As stated, this is not a theorem -- it is a definition dressed as a theorem.

**Severity:** High. The result as stated has no mathematical content beyond the definition. Either prove existence of the calibrator on the cube (which Corollary 5.4 essentially does), or restructure to make the logical flow honest.

### Non-blocker observations on correctness

- **Theorem 5.2 (Boundary rigidity):** The proof logic is sound -- the Stokes integral constraint plus the norm bound forces equality at every face. The step from "integral equals extremal value" to "integrand is constant" uses continuity and the fact that a continuous function bounded by $M$ whose integral over a unit cube equals $M$ must be identically $M$. This is correct.

- **Corollary 5.3 (Explicit minimizer):** The computation $d\eta_* = \omega_0$ is correct by direct differentiation. The norm computation is correct.

- **Theorem 6.1 (Dyadic readout):** The Stokes computation is correct. The volume inclusion $U_m(A) \subset A_{\sqrt{n} 2^{-m}}$ is correct. The Minkowski dimension formula is standard.

---

## 3. Editorial Blockers

### EDITORIAL-1: No author name

**Location:** Line 34

**Problem:** The `\author{}` field is empty. Cannot submit without author information.

### EDITORIAL-2: Bibliography is critically thin

**Location:** references_local.bib (4 entries total)

**Problem:** A paper of this scope -- touching de Rham theory, finite element exterior calculus, geometric measure theory, fractal geometry, Cheeger constants, and cubical cochains -- cites exactly four references, all textbooks. There are zero citations to:
- Prior work on sharp Poincare constants on convex bodies (Payne--Weinberger, Bebendorf, Veeser--Verfurth)
- Homotopy operators on cubes/simplices (Whitney 1957, Sullivan, Dupont)
- Cheeger constants and calibration methods (Cheeger 1970, Alter--Caselles--Chambolle, Parini)
- Cubical set theory / cubical cohomology (Kaczynski--Mischaikow--Mrozek, etc.)
- Minkowski content and box-counting dimension literature beyond Falconer's textbook
- The "companion manuscript" referenced in the abstract and introduction

This is unacceptable for any refereed journal. A reviewer would reject on bibliography alone.

### EDITORIAL-3: The "companion manuscript" is referenced but not cited

**Location:** Lines 41, 58--60, 113--117, 933--938

**Problem:** The paper repeatedly references "the scan-projection manuscript" and "the companion paper" but never provides a citation. This is a dangling reference. Either cite it (even as a preprint/arXiv) or remove all references to it.

### EDITORIAL-4: Abstract and introduction are too self-referential

**Location:** Lines 40--61, 65--141

**Problem:** The abstract and introduction spend significant space saying what the paper does *not* do ("deliberately stops at this deterministic geometric layer," "does not import the probabilistic scan-error machinery"). This defensive framing suggests the paper was extracted from a larger work and is trying to justify its existence. For a standalone journal submission, the paper should state what it *does* without apology. The discussion section (lines 918--938) repeats this defensive posture.

### EDITORIAL-5: Journal fit is questionable

**Problem:** The title references "JDSGT" in the directory name, but there is no well-known journal with this acronym. If this is the Journal of Differential Geometry, that journal publishes deep results with significant geometric content. This paper's main results (sharp homotopy operator bounds on the unit cube) are clean but not deep enough for JDG. The discrete corollaries (hypercube gradient consistency, near-detailed-balance) are more suited to a combinatorics or discrete mathematics journal. The dyadic readout section is geometric measure theory.

The paper's mixed audience (differential geometry + discrete math + fractal geometry) makes journal targeting difficult. A more natural home would be:
- **Advances in Mathematics** (if novelty concerns are addressed)
- **Journal of Geometric Analysis**
- **Proceedings of the AMS** (if shortened to the continuous results only)

### EDITORIAL-6: No MSC codes or keywords

**Problem:** Standard journal submissions require 2020 Mathematics Subject Classification codes and keywords. Both are missing.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### REC-1: Fix or replace Lemma 2.1

**Location:** Lines 190--203
**Problem:** The contraction estimate appears to be false as stated (see BLOCKER-1).
**Fix:** Work out $\iota_X \omega$ in coordinates explicitly. If the lemma is false, the sharp constant changes and the entire paper needs to be reworked. If there is a way to save it (e.g., by using a different norm, or by exploiting a cancellation I am missing), write it out in full detail with no hand-waving.

### REC-2: Expand the proof of Theorem 3.1 part (1)

**Location:** Lines 270--291
**Problem:** The step "Pullback by $H_t$ scales the $k-1$ tangential directions in $\iota_X \omega$ by $t^{k-1}$" is asserted without justification. For a reader who knows the Cartan formula this is "well-known," but the claim about the $t^{k-1}$ factor from pullback needs at least a one-line calculation.
**Fix:** Add 2--3 lines showing that $H_t^*(f(x) dx_J) = f(c + t(x-c)) \cdot t^{|J|} dx_J$ so that the $t^{k-1}$ factor is explicit.

### REC-3: Remove or restructure Proposition 5.1

**Location:** Lines 592--662
**Problem:** Tautological as stated (BLOCKER-4).
**Fix:** Option A: Remove the proposition entirely and simply state the duality as a remark after Corollary 5.3, noting that the explicit minimizer provides a calibrating field. Option B: Prove that a calibrating field exists for all bounded convex Lipschitz domains (this would be a genuinely new result but may be hard). Option C: State it as a definition/framework rather than a proposition.

### REC-4: Excise all "companion manuscript" language

**Location:** Lines 41, 58--60, 113--117, 933--938
**Problem:** Dangling reference, defensive framing.
**Fix:** Either cite the companion or remove all mentions. Rewrite the abstract and discussion to be self-contained. The paper should stand on its own merits without constantly explaining what it is *not*.

### REC-5: Expand the bibliography to at least 15--20 references

**Location:** references_local.bib
**Problem:** 4 references is far below journal standards.
**Fix:** Add citations for:
- Sharp Poincare/Sobolev constants on convex domains
- Whitney forms and simplicial/cubical de Rham theory
- Cheeger constant computation and calibration
- Cubical homology/cohomology
- Box-counting/Minkowski dimension
- Any prior work on homotopy operator norm bounds
- The companion manuscript

### REC-6: Add regularity discussion for Whitney forms in Section 4

**Location:** Lines 205--238 and 448--508
**Problem:** Whitney forms are piecewise smooth, not globally smooth. The transfer proof applies the smooth homotopy identity to Whitney forms without checking regularity.
**Fix:** Either (a) note that Whitney forms on the standard cubical complex are in fact smooth on $I^n$ (if true -- they are typically piecewise linear), or (b) extend the homotopy identity to piecewise smooth forms, or (c) work entirely at the cochain level without passing through smooth forms.

### REC-7: The probe form (eq 6.5) is just the standard volume primitive

**Location:** Lines 826--839
**Problem:** The "universal probe form" $\omega_0 = \frac{1}{n}\sum_i (-1)^{i-1} x_i dx_1 \wedge \cdots \widehat{dx_i} \cdots \wedge dx_n$ is the textbook primitive of the volume form. Presenting it as a discovery rather than a standard object overstates the contribution. The identity $\int_{\partial \Omega} \omega_0 = \mathrm{Vol}(\Omega)$ is just Stokes' theorem applied to $d\omega_0 = \mathrm{vol}$.
**Fix:** Acknowledge that this is the standard primitive and that the contribution is the combination with the dyadic approximation framework, not the form itself.

### REC-8: Table 1 -- "boundary minimizers" row is unclear

**Location:** Lines 124--140, specifically line 135
**Problem:** The row says "every minimizer of $d\eta = dx_1 \wedge \cdots \wedge dx_k$ has canonical face traces" with sharp constant $1/(2k)$. The constant $1/(2k)$ is the *value* of the minimal norm, not a "sharp constant" in the same sense as the other rows (which are operator norm bounds). This is confusing.
**Fix:** Clarify what $1/(2k)$ means in this row (minimal achievable norm) versus what it means in other rows (sharp operator norm bound).

---

## 5. Comparison with Prior Stage Notes

No P2/P3 notes exist for this paper. This is the first review.

**Observation:** The absence of a PIPELINE.md, JOURNAL_FIT.md, BIB_SCOPE.md, SOURCE_MAP.md, or THEOREM_LIST.md suggests this paper has not gone through the standard pipeline stages. It reads as a direct extraction from a larger project ("the companion manuscript") without the usual preparatory analysis.

---

## 6. Summary of Issues by Severity

### BLOCKER (must fix before resubmission)

| ID | Issue | Section |
|----|-------|---------|
| BLOCKER-1 | Contraction estimate (Lemma 2.1) appears false for k >= 2 | Sec 2.1 |
| EDITORIAL-2 | Bibliography has only 4 references | Global |
| EDITORIAL-3 | Companion manuscript cited but never referenced | Global |

### MEDIUM (significant but fixable)

| ID | Issue | Section |
|----|-------|---------|
| BLOCKER-2 | Sharpness in Thm 3.2 has logical gap | Sec 3.2 |
| BLOCKER-3 | Discrete transfer regularity gap | Sec 4.1 |
| BLOCKER-4 | Cheeger--Stokes duality is tautological | Sec 5.1 |
| REC-2 | Pullback scaling step needs calculation | Sec 3.1 |
| REC-6 | Whitney form regularity | Sec 2.2, 4.1 |

### MINOR (polish items)

| ID | Issue | Section |
|----|-------|---------|
| EDITORIAL-1 | No author name | Title page |
| EDITORIAL-4 | Defensive "companion" framing | Abstract, Intro, Discussion |
| EDITORIAL-5 | Journal fit unclear | Global |
| EDITORIAL-6 | No MSC codes or keywords | Title page |
| REC-7 | Probe form is standard, not novel | Sec 6 |
| REC-8 | Table 1 row 5 unclear | Sec 1 |

---

## 7. Verdict Rationale

The paper attempts a clean, self-contained chain from cubical homotopy operators to dyadic dimension readout. The writing is disciplined, the structure is logical, and the scope is deliberately narrow.

**BLOCKER-1 is fatal and confirmed by explicit computation.** The contraction estimate in Lemma 2.1 is false, and consequently Theorem 3.1 part (2) -- the main result of the paper -- is false. A concrete counterexample is given above: on $I^3$ with $\omega = dx_1 \wedge dx_3 + dx_2 \wedge dx_3$, we have $\|K_2\omega\|_\infty = 1/3 > 1/4 = \frac{1}{2k}\|\omega\|_\infty$.

Every downstream result (Theorems 3.2, 4.1, Corollaries 3.3, 4.2, Theorem 4.3, and the discrete transfer) depends on this bound and is therefore unproven.

The bibliography deficit (4 references) is independently sufficient for a desk reject.

The paper needs to return to P2 (mathematical development) with one of these strategies:
1. **Use a different norm** (e.g., the comass norm $\|\omega\|_* = \sup_{|v_i|\le 1} |\omega(v_1,\ldots,v_k)|$) for which the contraction estimate might hold.
2. **Restrict to decomposable forms** where the lemma is correct, and restate all theorems accordingly.
3. **Find the correct constant** for the coefficient sup norm, which will be dimension-dependent, and rebuild the theorem chain.

**Decision: REJECT -- return to P2**

Top 3 blockers for TRACK_BOARD:
1. Theorem 3.1 main bound $1/(2k)$ is FALSE (counterexample: $\omega = dx_1 \wedge dx_3 + dx_2 \wedge dx_3$ on $I^3$)
2. Lemma 2.1 contraction estimate is false for non-decomposable forms
3. Bibliography has only 4 textbook references (desk-reject level)

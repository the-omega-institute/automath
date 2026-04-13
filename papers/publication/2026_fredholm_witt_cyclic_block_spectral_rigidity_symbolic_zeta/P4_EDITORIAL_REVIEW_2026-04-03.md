# P4 Editorial Review -- Claude Gate 3

**Paper:** Fredholm determinants, cyclic-block realisations, and spectral rigidity for symbolic zeta-functions
**Date:** 2026-04-03
**Reviewer:** Claude (independent verification, Gate 3)
**Prior review:** ChatGPT o3-mini-high (Gate 2, 2026-04-02) -- verdict REJECT

---

## I. Summary

The paper develops three operator-theoretic results around symbolic dynamical zeta-functions:

1. **Fredholm--Witt bridge** (Thm 3.1): For trace-class $T$, the Fredholm determinant $\det(I - zT)^{-1}$ equals the exp-trace generating function, which equals an Euler product in the Mobius-inverted "Witt coordinates" $p_n(T)$.

2. **Cyclic-block realisation** (Thm 3.3): Any Euler product $\prod_j (1 - \beta_j z^{n_j})^{-m_j}$ satisfying a trace-class summability condition is realised by an explicit direct sum of cyclic blocks.

3. **Spectral rigidity** (Thm 3.7): Equality of Fredholm determinants for two trace-class operators forces equality of non-zero spectra with algebraic multiplicity.

Two applications are given: a group-inverse gradient formula for finite-part constants under holomorphic deformation of primitive matrices (Thm 4.1--4.2), and a spectral-gap CLT for locally constant observables on mixing subshifts (Prop 4.3).

---

## II. Mathematical Correctness Assessment

### Theorem 3.1 (Fredholm--Witt bridge): CORRECT

The identity $\det(I - zT)^{-1} = \exp(\sum a_n z^n / n)$ is classical for trace-class operators (Grothendieck, Simon). The passage from trace generating function to Euler product via Mobius inversion is a standard formal identity. The proof is complete and correct.

**One caveat:** The Euler product $\prod_{n \ge 1}(1 - z^n)^{-p_n(T)}$ requires care in interpretation when $p_n(T)$ is complex (which it can be for general trace-class $T$). The authors should note that $(1 - z^n)^{-p_n(T)} := \exp(-p_n(T) \log(1 - z^n))$ with principal branch, and that the product converges absolutely in the stated disk because $\sum |p_n(T)| \cdot |z|^n < \infty$ follows from trace-class estimates. This is implicit but deserves a sentence.

### Theorem 3.3 (Cyclic-block realisation): CORRECT

The construction is clean. The key computation: $C(n, \alpha) = \alpha \Pi_n$ has eigenvalues $\alpha \omega^k$ where $\omega = e^{2\pi i/n}$, hence $\det(I - zC(n,\alpha)) = 1 - \alpha^n z^n$. Tensoring with $I_m$ gives multiplicity $m$. Direct sums give products of determinants. The trace-norm computation $\|L_{\mathcal{D}}\|_1 = \sum m_j n_j |\alpha_j| = \sum m_j n_j |\beta_j|^{1/n_j}$ is correct since all singular values of $\alpha \Pi_n$ equal $|\alpha|$.

### Theorem 3.7 (Spectral rigidity): CORRECT

This follows from the canonical product representation of trace-class Fredholm determinants (Simon, Thm 3.7). The zeros of $\det(I - zT)$ are exactly $\{\lambda_k^{-1}\}$ with algebraic multiplicity. Equality of entire functions of order at most 1 means same zeros with multiplicity. The argument is correct but short -- it is essentially a citation of Simon's result combined with the identity theorem.

### Proposition 2.1 and Lemma 2.2: CORRECT

Standard Perron--Frobenius and Mobius inversion. The error term in Lemma 2.2 correctly captures both the sub-Perron spectral radius $\Lambda(A)^n$ and the $\lambda^{n/2}$ contribution from divisors $d \ge 2$.

### Theorem 2.4 (Finite-part closed form): CORRECT

The proof is correct. The elementary identity $\sum_{k \ge 1} (\mu(k)/k) \log(1 - x^k) = -x$ for $|x| < 1$ is valid; it follows from Mobius inversion of $-\log(1-x) = \sum x^n/n$. The parenthetical explanation in the paper is adequate but could be cleaner (agreeing with ChatGPT's M4 concern).

### Theorem 4.1 (Gradient formula): CORRECT

The use of the group inverse $B_\theta^\#$ is standard (Campbell--Meyer). The reduced determinant $\det'(B_\theta) = \prod_{\mu \ne \lambda}(1 - \mu/\lambda)$ is indeed $C(A_\theta)^{-1}$ by equation (6). The logarithmic derivative $\partial_\theta \log \det'(B_\theta) = \operatorname{Tr}(R_\theta \partial_\theta B_\theta)$ is the standard Jacobi formula restricted to the spectral complement. The sign computation involving two cancelling negatives is correct.

**Minor issue:** The reduced determinant $\det'$ is used without formal definition. ChatGPT's M2 concern is valid -- a one-line definition would improve readability.

### Theorem 4.2 (Holomorphic variation of Abel finite part): CORRECT

The normal convergence argument for the Mobius series at $k \ge 2$ is correct: $|\lambda(\theta)^{-k}| \le \lambda_{\min}^{-2}$ ensures uniform convergence in $\theta$. The resolvent derivative formula follows from Jacobi's formula in finite dimension.

**Issue:** The proof's last step invokes $\log \det(I - zA_\theta)^{-1} = -\operatorname{Tr} \log(I - zA_\theta)$ and "differentiate inside the trace." This is valid in finite dimension, but as stated it is sloppy -- one should invoke Jacobi's formula directly without the matrix logarithm. ChatGPT's M3 concern is valid.

### Proposition 4.3 (Spectral-gap CLT): CORRECT but INCOMPLETE

The statement is correct and the result is indeed standard. The proof sketch correctly identifies the mechanism: analytic perturbation of the dominant eigenvalue of the twisted transfer operator, $\lambda'(0) = 0$ from centering, $\sigma_f^2 = \lambda''(0)/\lambda(0) > 0$ from non-coboundary assumption, then Nagaev--Guivarc'h method.

However, the proof of the **exponential decay of characteristic functions** away from the origin is genuinely incomplete. The key step -- showing $\rho(\mathcal{L}_{it}) < \lambda(0)$ for $t \ne 0$ via the coboundary characterization -- is not carried out. ChatGPT's B2 concern is valid: this is the one argument that requires real work (the Perron--Frobenius comparison argument), and it is entirely omitted.

---

## III. Evaluation of ChatGPT's Concerns

| ChatGPT ID | Valid? | Assessment |
|------------|--------|------------|
| B1 (Insufficient novelty) | **Partially valid** | The novelty concern is legitimate but overstated. The individual theorems are indeed close to classical, but the *packaging* -- the existence-vs-rigidity trichotomy and the explicit cyclic-block converse -- has value as a clean organizational contribution. However, for a *research journal* (as opposed to expository), the novelty is indeed thin. For a venue like Proceedings of the AMS or a short communication, the novelty bar is lower and could be met. |
| B2 (CLT proof incomplete) | **Valid** | The exponential decay of characteristic functions requires the strict spectral-radius drop for $\mathcal{L}_{it}$, which is the substantive step. Its omission is a real gap. |
| B3 (Remark 3.4 speculative) | **Partially valid but overrated** | The remark is clearly *labeled* as a remark and uses hedging language ("could realise"). It is not asserting a theorem. Converting it to an explicit open question would be cleaner, but calling this a "BLOCKER" is too strong. |
| M1 (Vague Thm 1.2 statement) | **Valid** | The phrase "adding the absolutely convergent higher-order Fredholm corrections" in Theorem 1.2 is imprecise for a theorem statement. The full formula appears in Thm 4.2 and should be included or referenced precisely. |
| M2 (Undefined reduced det) | **Valid** | $\det'$ should be defined explicitly. |
| M3 (Matrix log in Thm 4.2) | **Valid** | Should use Jacobi's formula directly. |
| M4 (Elementary identity garbled) | **Mildly valid** | The parenthetical is not "garbled" -- it is readable but could be streamlined. |
| M5 (Redundant $r_{\mathcal{D}} < \infty$) | **Valid but minor** | Correct that the finiteness follows from summability. |
| M6 (Extension claims in Sec 5) | **Mildly valid** | The extensions are plausible and clearly conjectural. Tightening the language is good practice but not critical. |
| L1--L4 | **All valid, all minor** | Standard polish items. |

### ChatGPT False Positives

- **B1 as an absolute REJECT**: The novelty assessment is calibrated for a top-tier research journal. For a short note or proceedings contribution, the paper *could* be appropriate. ChatGPT does not differentiate venue tiers.
- **B3 as BLOCKER**: Overstated. The remark is clearly framed as speculative and does not affect any theorem.

### ChatGPT Valid Concerns Underweighted

- **The CLT characteristic-function decay** (B2) is the most serious mathematical issue. This is not just a matter of exposition -- the key spectral-radius strict inequality is a genuine argument that uses the non-coboundary condition in a non-trivial way (via Perron comparison on the moduli matrix). Its complete omission means the proof of half of Proposition 4.3 is missing.

---

## IV. Novelty Assessment

| Result | Novelty | Rationale |
|--------|---------|-----------|
| Thm 3.1 (Fredholm--Witt bridge) | **LOW** | Classical identity reformulated with explicit Witt coordinates. Authors acknowledge this. |
| Thm 3.3 (Cyclic-block realisation) | **MEDIUM** | The explicit construction is elementary but the result itself -- that *every* Euler product under trace-class summability admits a concrete operator model -- appears to be new as a stated theorem. The observation is useful and the construction is clean. |
| Thm 3.7 (Spectral rigidity) | **LOW** | Direct consequence of Simon's canonical product theorem. The "spectral rigidity" framing adds conceptual clarity but no mathematical content beyond the citation. |
| Thm 2.4 (Finite-part closed form) | **MEDIUM** | The connection between the Abel finite-part constant $\log \mathcal{M}(A)$ and $\log C(A)$ plus Mobius-weighted Fredholm corrections is a clean identity. Not deep but useful. |
| Thm 4.1 (Gradient formula) | **MEDIUM-LOW** | Standard perturbation theory applied via the group inverse. The formula itself may not have been written down explicitly in this form, but it follows immediately from known tools. |
| Thm 4.2 (Abel finite-part variation) | **LOW** | Termwise differentiation of Thm 2.4. |
| Prop 4.3 (CLT) | **LOW** | Authors explicitly state this is standard. |

**Aggregate novelty:** The paper's contribution is primarily *organizational* -- it isolates the operator-theoretic core from the finite-state category and packages the existence/rigidity trichotomy cleanly. The strongest original content is Theorem 3.3. This level of novelty is appropriate for a short note in a venue such as *Proceedings of the AMS*, *Bulletin of the AMS (research announcement)*, or *Comptes Rendus Mathematique*, but likely insufficient for journals like *Advances in Mathematics*, *JEMS*, or *Inventiones*.

---

## V. Specific Improvements Required

### Critical (must fix before resubmission)

**C1. Complete the proof of Prop 4.3 characteristic-function decay.**
The exponential decay assertion requires proving $\rho(\mathcal{L}_{it}) < \rho(\mathcal{L}_0)$ for $t \ne 0$, uniformly on compacts. This is the Perron--Frobenius comparison argument: if $\rho(\mathcal{L}_{it}) = \rho(\mathcal{L}_0)$, then $|e^{itf}|$ must factor as a coboundary times a constant phase on allowed edges, forcing $f$ to be a coboundary modulo constants. Either write this out (4--6 lines in finite dimension) or give a precise citation with theorem number.

**C2. Define the reduced determinant $\det'(B_\theta)$ before Theorem 4.1.**
Insert: $\det'(B_\theta) := \prod_{\nu \in \operatorname{spec}(B_\theta) \setminus \{0\}} \nu$, then show $C(A_\theta) = \det'(B_\theta)^{-1}$ from equations (5)--(6).

**C3. Replace the matrix-logarithm argument in Theorem 4.2 proof with Jacobi's formula.**
Use $\partial_\theta \det(I - zA_\theta) = \det(I - zA_\theta) \operatorname{Tr}((I - zA_\theta)^{-1}(-z\partial_\theta A_\theta))$ directly.

### Important (should fix)

**I1. Clarify the Euler product interpretation in Thm 3.1.**
When $p_n(T) \notin \mathbb{Z}$, the factors $(1 - z^n)^{-p_n(T)}$ require a branch choice. State that $(1 - w)^{-c} := \exp(-c \log(1-w))$ with principal branch, and that the product converges absolutely for $|z| < \|T\|^{-1}$.

**I2. Sharpen Theorem 1.2 in the introduction.**
Replace "obtained by adding the absolutely convergent higher-order Fredholm corrections" with the explicit formula from Theorem 4.2, or write "the precise formula is given in Theorem 4.2 below."

**I3. Streamline the elementary identity in Theorem 2.4 proof.**
The parenthetical explanation can be replaced by a direct two-line computation:
$$
-\sum_{k \ge 1} \frac{\mu(k)}{k} \log(1 - x^k) = \sum_{k \ge 1} \frac{\mu(k)}{k} \sum_{r \ge 1} \frac{x^{kr}}{r} = \sum_{n \ge 1} \frac{x^n}{n} \sum_{k \mid n} \mu(k) = x.
$$

**I4. Add missing references for the CLT/spectral-gap machinery.**
Suggested additions: Hennion--Herve (2001) for the spectral-method CLT framework; a Livsic-type reference for the coboundary characterization used implicitly in Prop 4.3.

**I5. Convert Remark 3.4's speculative claim to an explicit open question.**
Current: "other operator models ... could realise the same Fredholm determinant under weaker summability hypotheses."
Better: "Whether trace-class realisability of a given Euler product can be achieved under strictly weaker summability conditions via non-cyclic constructions remains an open question."

### Minor (polish)

**P1.** In Remark 3.6 (choice of roots), the sentence about unitary inequivalence could note that the *spectra* may differ while the *multisets of eigenvalues* (counting algebraic multiplicity) agree -- this is what spectral rigidity gives.

**P2.** The "Further remarks" section (Sec 5) should temper the claims about nuclear Banach-space extensions and Axiom A flows. These are plausible but unproved; label them as open directions, not as extensions that "carry over."

**P3.** Lemma 2.2 should state that the implied constant depends on the spectral data of $A$ (or simply on $A$).

---

## VI. Assessment of Paper's Logical Structure

The paper's organizational thesis -- separating the operator-theoretic layer (trace sequences, Witt coordinates, Fredholm determinants) from the finite-state layer (non-negativity, integrality, orbit counting) -- is sound and genuinely useful for the field. The existence-vs-rigidity picture (Thm 3.3 vs Thm 3.7) is a clean conceptual contribution.

The dependency chain is:
- Sec 2 (finite-state): self-contained, clean
- Sec 3 (operator-theoretic core): Thm 3.1 depends on classical Fredholm theory; Thm 3.3 is a new construction; Thm 3.7 depends on Simon's canonical product theorem
- Sec 4 (applications): depends on Sec 2 and Sec 3 only through standard perturbation theory; logically independent of the operator-theoretic core except for motivation

The paper correctly identifies that Sec 4 uses the spectral-gap mechanism common to both the gradient formula and the CLT, but this observation is more pedagogical than mathematical.

---

## VII. Verdict

$$
\boxed{\text{MINOR\_REVISION}}
$$

**Rationale:** The paper is mathematically correct in all its main theorems (with the exception of an incomplete proof in Prop 4.3). The writing is clean, the logical structure is clear, and the organizational contribution -- the existence-vs-rigidity trichotomy for Fredholm determinants in the symbolic context -- has genuine value. The novelty is modest but real, centered on Theorem 3.3.

I disagree with ChatGPT's REJECT verdict. ChatGPT calibrated its novelty assessment for a top-tier research journal, which is fair in that context. However, the paper is well-suited as a short note for a venue like *Proceedings of the AMS* or *Comptes Rendus*. For such a venue, the paper needs:

1. The three critical fixes (C1--C3) above
2. The important improvements (I1--I5)
3. Appropriate venue targeting

If the authors intend to submit to a higher-tier journal, I would agree with ChatGPT that Theorem 3.3 needs substantial strengthening -- e.g., a minimality or uniqueness result for cyclic-block realisations, or a characterization of which Euler products admit trace-class realisation under weaker conditions.

**Disposition for pipeline:** Proceed to revision (P5) with fixes C1--C3 and I1--I5. Target a short-note venue. If higher-tier venue is desired, a deeper result around Theorem 3.3 is needed first.

---

## VIII. Cross-Gate Comparison

| Dimension | ChatGPT (Gate 2) | Claude (Gate 3) |
|-----------|-------------------|-----------------|
| Mathematical correctness | No errors found | No errors found (incomplete proof in 4.3 noted by both) |
| Novelty | REJECT-level | Modest but sufficient for short-note venue |
| Thm 3.1 | LOW | LOW (agree) |
| Thm 3.3 | MEDIUM-LOW | MEDIUM (slightly higher -- the explicit construction filling a gap in the literature is useful) |
| Thm 3.7 | LOW | LOW (agree) |
| Thm 4.1 | MEDIUM-LOW | MEDIUM-LOW (agree) |
| Prop 4.3 | LOW | LOW (agree) |
| Proof completeness | B2 flagged correctly | Confirm B2, identify mechanism gap precisely |
| Overall | REJECT | MINOR_REVISION (venue-dependent) |
| Key disagreement | Paper cannot be saved without deeper theorem | Paper is publishable as-is (with fixes) in appropriate venue |

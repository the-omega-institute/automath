# P4 Editorial Review Round 3 -- Claude Gate 3 (Final Verification)

**Paper:** Fredholm determinants, cyclic-block realisations, and spectral rigidity for symbolic zeta-functions
**Date:** 2026-04-03
**Reviewer:** Claude (independent verification, Gate 3, Round 3)
**Prior reviews:** ChatGPT o3-mini-high (Gate 2, REJECT); Claude R1 (Gate 3, MINOR_REVISION); Claude R2 (Gate 3, MINOR_REVISION -- 2 issues remaining)
**Scope:** Confirm that the two R2 issues (NEW-1 and NEW-3) are correctly resolved, and perform a final global check

---

## I. Targeted Verification of R2 Fixes

### NEW-1 -- Theorem 3.5 vacuous minimality framing

**R2 diagnosis:** The inequality $\le$ was misleading because all block-cyclic normal realisations have equal trace norm. R2 recommended reframing as a rigidity/invariance statement.

**Current state (sec_fredholm.tex, lines 148--159):**

The theorem is now titled "Trace-norm rigidity of block-cyclic normal realisations" and states:

> Every block-cyclic normal realisation $L$ of $\mathcal{D}$ ... has the same trace norm:
> $$\|L\|_1 = \sum_{j \in J} m_j n_j |\beta_j|^{1/n_j}.$$
> In particular, the trace norm is an invariant of the Euler data $\mathcal{D}$, independent of the choice of roots or block ordering.

**Assessment: FIX IS CORRECT AND COMPLETE.**

- The $\le$ has been replaced by $=$ (equality, not inequality).
- The title and closing sentence now frame this as rigidity/invariance, not optimality.
- The proof (lines 161--180) is unchanged and correctly establishes equality for every realisation in the class.
- No overclaiming remains.

---

### NEW-3 -- Sign error in intermediate display of Theorem 4.2 proof

**R2 diagnosis:** The proof had $\partial_\theta \log \det'(B_\theta) = -\Tr(R_\theta \partial_\theta B_\theta)$ with a spurious minus sign. Jacobi's formula gives $+\Tr$. The final formula was correct due to double negation, but the intermediate step was wrong.

**Current state (sec_perturbation.tex, lines 60--71):**

The proof now reads:

$$
\partial_\theta \log \det'(B_\theta) = \Tr(R_\theta \, \partial_\theta B_\theta).
$$

followed by

$$
\partial_\theta \log C(A_\theta) = -\partial_\theta \log \det'(B_\theta) = -\Tr(R_\theta \, \partial_\theta B_\theta),
$$

**Verification of the full sign chain:**

1. Jacobi's formula: $\partial_\theta \log \det(M) = \Tr(M^{-1} \partial_\theta M)$ for invertible $M$.
   Applied to $M = B_\theta|_{(I-P_\theta)\mathbb{C}^d}$ (invertible on the spectral complement) with inverse $R_\theta$:
   $$\partial_\theta \log \det'(B_\theta) = +\Tr(R_\theta \, \partial_\theta B_\theta). \quad\checkmark$$

2. Since $C(A_\theta) = \det'(B_\theta)^{-1}$:
   $$\partial_\theta \log C = -\partial_\theta \log \det' = -\Tr(R_\theta \, \partial_\theta B_\theta). \quad\checkmark$$

3. Substituting $\partial_\theta B_\theta = -\partial_\theta A_\theta / \lambda + (\partial_\theta \lambda / \lambda^2) A_\theta$:
   $$-\Tr\bigl(R_\theta(-\partial_\theta A_\theta / \lambda + (\partial_\theta \lambda / \lambda^2) A_\theta)\bigr) = \Tr\bigl(R_\theta(\partial_\theta A_\theta / \lambda - (\partial_\theta \lambda / \lambda^2) A_\theta)\bigr). \quad\checkmark$$

4. This matches the stated formula (lines 39--44). $\checkmark$

**Assessment: FIX IS CORRECT. The sign chain is now clean throughout.**

---

## II. Global Theorem-by-Theorem Verification (post-R2 state)

### Section 2 (Preliminaries)

**Proposition 2.1** (Trace, primitive orbits, Euler product): Standard exp-trace identity for finite matrices, Mobius inversion algebra. **CORRECT.**

**Lemma 2.2** (Primitive orbit asymptotic): Perron main term $\lambda^n/n$, error from divisors $d \ge 2$ contributing $O(\lambda^{n/2}/n)$, Jordan-data dependence of implied constant stated. **CORRECT.**

**Theorem 2.4** (Primitive-orbit closed form): The Mobius inversion computation $\sum_{k \ge 1} \frac{\mu(k)}{k} \log(1-x^k) = -x$ is displayed explicitly (lines 176--181). The Abel limit argument separating $k=1$ from $k \ge 2$ is clean. The second identity via Euler product is verified. **CORRECT.**

### Section 3 (Fredholm Determinants and Cyclic-Block Realisations)

**Theorem 3.1** (Fredholm--Witt bridge): Classical identity for trace-class operators, Mobius inversion identical. **CORRECT.**

**Theorem 3.3** (Cyclic-block Fredholm realisation): The key identity $\det(I - zC(n,\alpha)) = 1 - \alpha^n z^n$ follows from the eigenvalues of $\alpha \Pi_n$ being $\{\alpha \omega^k\}_{k=0}^{n-1}$, giving $\prod_k(1 - \alpha \omega^k z) = 1 - (\alpha z)^n$. Trace-norm computation and convergence radius are correct. Finiteness of $r_{\mathcal{D}}$ from summability is noted parenthetically. **CORRECT.**

**Definition 3.4** (Block-cyclic normal realisation): Clean definition constraining the class. **CORRECT.**

**Theorem 3.5** (Trace-norm rigidity): Verified in detail above. Equality statement, rigidity framing. **CORRECT.**

**Remark 3.6** (Sharpness): States that the summability condition is sharp for the specific construction; leaves open whether weaker hypotheses suffice in other models. Clean open question, no unproved assertions. **CORRECT.**

**Remark 3.7** (Choice of roots): Different $n_j$th roots give the same multiset of eigenvalues (since $\{\alpha \omega^k\}_{k=0}^{n-1}$ is invariant under $\alpha \to \alpha \omega$). Forward reference to spectral rigidity theorem is appropriate. **CORRECT.**

**Theorem 3.8** (Spectral rigidity): Identity theorem extends germ equality to all of $\mathbb{C}$. Canonical product representation (Simon, Thm 3.7) recovers zeros with multiplicity. Trace-sequence equality from log-expansion. **CORRECT.**

**Corollary 3.9** (Realisability versus rigidity): Immediate consequence. **CORRECT.**

### Section 4 (Perturbative Applications)

**Definition 4.1** (Reduced determinant): $\det'(B_\theta) = \prod_{j=2}^d \nu_j(\theta)$ with $C(A_\theta) = \det'(B_\theta)^{-1}$. Consistent with equation (6) in preliminaries. **CORRECT.**

**Theorem 4.2** (Gradient formula): Full sign chain verified in detail above. Group inverse properties ($R_\theta P_\theta = 0$, $P_\theta R_\theta = 0$) justify equating the restricted Jacobi computation with $\Tr(R_\theta \partial_\theta B_\theta)$. The Perron eigenvalue derivative $\partial_\theta \lambda = \ell_\theta^T (\partial_\theta A_\theta) r_\theta$ is standard Kato perturbation theory. **CORRECT.**

**Theorem 4.3** (Holomorphic variation of Abel finite part): Uses Theorem 2.4 applied to each $A_\theta$. Jacobi's formula for $\Phi_k$ with the explicit resolvent form is now given (lines 128--134). Convergence bound $|\frac{\mu(k)}{k} \partial_\theta \Phi_k| \le C_1/(k \lambda_{\min}^k) + C_2/\lambda_{\min}^{k-1}$ is exponentially decaying. Termwise differentiation justified. **CORRECT.**

**Proposition 4.4** (CLT): Recoding to one-step function, weighted matrices $M_t$, Perron comparison $\rho(t) \le \lambda$, Wielandt equality case forcing coboundary via Livsic, Jordan-norm exponential decay, analytic perturbation near $t=0$ with $\lambda(0)=\lambda$, $\lambda'(0)=0$, $\lambda''(0) = \sigma_f^2 \lambda > 0$, Levy continuity. All steps verified in R2 and unchanged. **CORRECT.**

---

## III. Status of Residual LOW Issues from R2

| ID | R2 Severity | Current Status | Assessment |
|----|-------------|----------------|------------|
| PERSIST-1 | LOW | Branch convention for $(1-z^n)^{-p_n(T)}$ when $p_n \notin \mathbb{Z}$ still not explicitly stated in Theorem 3.1. | The proof goes through the exp-trace representation, not the Euler product directly, so the mathematics is unambiguous. This is an expositional nicety, not a correctness issue. **Acceptable for Proc. AMS** -- a referee might request a footnote, but this does not block acceptance. |
| PERSIST-2 | LOW | Campbell--Meyer 1979 is in the .bib but not cited in the text. | Harmless. LaTeX/BibTeX will simply omit it from the printed references. No action needed. |
| NEW-2 | LOW | Theorem 1.2 still says "obtained by adding the absolutely convergent higher-order Fredholm corrections" without forward reference to Theorem 4.3. | Checked: lines 108--109 of sec_introduction.tex confirm the vague phrasing persists. However, the reader is directed to Section 4 by the paper's organisation subsection (line 170--172). This is a minor expositional point that a copyeditor can address. **Does not block acceptance.** |
| NEW-4 | LOW | Ruelle1969 bib entry: title "Axiom A and transfer-operator spectra" does not match the actual 1969 Ruelle paper. | Confirmed: The Ruelle 1969 paper in Comm. Math. Phys. 13 is "Statistical mechanics of a one-dimensional lattice gas," not the title given. However, the citation is used in a cluster reference alongside Keller--Liverani and Hennion--Herve for spectral perturbation theory, and the journal/volume/pages (Comm. Math. Phys. 13, 177--203) are consistent with the actual paper. **The title should be corrected in proofs but does not affect mathematical content.** |

None of these residual issues are blocking.

---

## IV. Cross-Reference and Numbering Check

All `\Cref` labels are stable (label-based, not number-based):
- `thm:fredholm-spectral-rigidity` -- Theorem 3.8
- `thm:cyclic-fredholm-realisation` -- Theorem 3.3
- `thm:block-cyclic-rigidity` -- Theorem 3.5
- `def:block-cyclic-normal-realisation` -- Definition 3.4
- `thm:clt-spectral` -- Proposition 4.4
- `thm:finite-part-primitive-closed-form` -- Theorem 2.4
- `thm:finite-part-reduced-determinant-group-inverse-gradient` -- Theorem 4.2
- `thm:logM-holomorphic-variation` -- Theorem 4.3
- `rem:choice-of-roots` references `thm:fredholm-spectral-rigidity` -- correct forward reference

No orphaned or broken references detected.

---

## V. Proc. AMS Format and Style Check

- **Length:** 6 .tex files, each well under 800 lines; total content appropriate for Proc. AMS (short communications).
- **amsart document class:** Correct.
- **Subject classification:** 37B10 (symbolic dynamics), 47B10 (trace-class), 47A55 (perturbation theory), 60F05 (CLT). Appropriate.
- **Keywords:** Relevant and specific.
- **Abstract:** Concise, states main results without excessive generality.
- **Proof style:** Appropriate level of detail for the venue. No gaps remain.
- **Notation:** Consistent throughout ($\sone$, $B_\theta^\#$, $\MM$, $C(A)$, $\det'$).
- **No revision traces, changelogs, or meta-commentary in the .tex files.**

---

## VI. Final Assessment

### Issues fully resolved across R1-R2-R3

| Original ID | Resolution |
|-------------|-----------|
| B1 (Strengthen Theorem 3.3) | RESOLVED -- Theorem 3.5 added as trace-norm rigidity |
| B2 (CLT proof incomplete) | RESOLVED -- proof complete with Wielandt/Livsic argument |
| B3 (Speculative remark) | RESOLVED -- converted to open question |
| M1 (Vague Thm 1.2) | RESOLVED -- gradient formula explicit |
| M2 (Undefined reduced det) | RESOLVED -- Definition 4.1 added |
| M3 (Matrix-log argument) | RESOLVED -- Jacobi used correctly |
| M4 (Garbled identity) | RESOLVED -- clean Mobius computation |
| M5 (Redundant $r_{\mathcal{D}} < \infty$) | RESOLVED -- parenthetical explanation |
| M6 (Extension overreach) | RESOLVED -- hedged language |
| NEW-1 (Vacuous minimality) | RESOLVED -- reframed as trace-norm rigidity with equality |
| NEW-3 (Sign error in intermediate step) | RESOLVED -- sign corrected, chain verified |

### Remaining observations (all LOW, non-blocking)

| ID | Description | Action |
|----|-------------|--------|
| PERSIST-1 | Branch convention for non-integer Witt exponents | Optional footnote in proofs |
| NEW-2 | Forward reference to Thm 4.3 in Thm 1.2 | Copyediting polish |
| NEW-4 | Ruelle1969 bib title incorrect | Correct in proofs |

These are standard proof-stage corrections that do not require re-review.

---

## VII. Verdict

$$
\boxed{\text{ACCEPT}}
$$

**Rationale:**

All mathematical content is correct. Every theorem, proposition, lemma, and corollary has been verified across three rounds of review. The two substantive issues from R2 have been properly resolved:

1. **Theorem 3.5** is now honestly framed as trace-norm rigidity (equality, not a vacuous inequality), with the title, statement, and commentary all consistent.

2. **The Jacobi sign chain** in the Theorem 4.2 proof is now clean: $\partial_\theta \log \det' = +\Tr(R_\theta \partial_\theta B_\theta)$, then $\partial_\theta \log C = -\Tr(R_\theta \partial_\theta B_\theta)$, yielding the correct gradient formula after substituting $\partial_\theta B_\theta$.

The paper makes a clear, honest contribution: systematic separation of the Fredholm--Witt bridge, cyclic-block converse realisation, and spectral rigidity -- three statements that are classical individually but are here cleanly isolated and made explicit. The two perturbative applications (gradient formula and CLT) are standard but well-presented as illustrations of the common spectral-gap mechanism. The writing is appropriate for Proceedings of the AMS: concise, self-contained, and free of overclaiming.

The three remaining LOW observations (branch convention footnote, forward reference in Thm 1.2, bib title correction) are routine proof-stage fixes that do not affect mathematical substance and do not require further review.

**The paper is ready for submission to Proceedings of the AMS.**

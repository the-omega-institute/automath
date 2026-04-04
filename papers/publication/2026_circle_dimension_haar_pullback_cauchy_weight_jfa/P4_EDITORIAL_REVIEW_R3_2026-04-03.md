# P4 Editorial Review -- Round 3 Final Verification

**Paper:** Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS

**Target:** Journal of Functional Analysis (JFA)

**Date:** 2026-04-03

**Reviewer:** Claude Gate 3 (Round 3 -- final verification pass)

**Prior reviews:** ChatGPT v40 recheck (8 issues: I1--I8); Claude R1 editorial review (4 new issues: N1--N4)

---

## 1. Decision

**ACCEPT** (subject to one cosmetic fix surviving from R1)

---

## 2. Issue-by-Issue Verification

### I1: Bibliography -- no [?] placeholders

**STATUS: RESOLVED**

The `references.bib` file contains 27 complete entries. Every `\cite{}` key in the LaTeX source has a matching bib entry. Verified all cite keys against the bib file:

- Aronszajn1950, ArtsteinBallBartheNaor2004, AldroubiGrochenig2001, Barron1986 -- present
- BobkovChistyakovGotze2013, BobkovChistyakovGotzeBerryEsseen2014, BobkovChistyakovGotzeEdgeworth2013, Bownik2000 -- present
- Folland1995, Feller1971, Duren1970, deBoorDeVoreRon1994, Grafakos2014 -- present
- JohnsonBarron2004, FuhrGrochenigHaimiKlotzRomero2018, GrochenigRomeroStockler2020 -- present
- Lukacs1970, Rudin1987, RonShen1995 -- present
- KiselevMininNovikov2016, KiselevMininNovikov2019, RomeroUlanovskiiZlotnikov2024, BaranovBelovGrochenig2022 -- present
- Stein1971, Toscani2016, Toscani2015, Widder1941 -- present

Zero `[?]` in LaTeX source. The ChatGPT review was against a compiled PDF where bibtex had not been run -- a build-process issue. A full `pdflatex + bibtex + pdflatex + pdflatex` cycle resolves it. No content changes needed.

### I2: Theorem 6.3 span vs. closed span

**STATUS: RESOLVED**

The current statement of Theorem 6.3 (`thm:mode-space-rkhs`, sec_gram_space.tex line 144) defines:

$$\mathcal{S} := \overline{\operatorname{span}}\{\Psi_\varepsilon : \varepsilon \in \mathbb{R}\}$$

This is explicitly the **closed** span (using `\overline{\operatorname{span}}`). The theorem then asserts $\mathcal{S} = L^2_0(\omega)$ and that $\mathcal{U}_0$ extends to a unitary $\mathcal{U}: L^2_0(\omega) \to \mathcal{H}_K$.

The proof correctly argues: (1) $\mathcal{S}^\perp = \{0\}$ via Poisson regularization and Fourier injectivity, hence $\mathcal{S} = L^2_0(\omega)$; (2) isometry on the algebraic span extends by density and continuity to the closed span, giving a surjective isometry (unitary).

This is mathematically correct and addresses the ChatGPT objection in full. The span-vs-closure error flagged in the review no longer exists.

### I3: Theorems 7.4--7.5 closed spans and Riesz basis formulation

**STATUS: RESOLVED**

Theorem 7.4 (`thm:poisson-lattice-sampling`, sec_strip_lattice.tex line 247) defines:

$$\mathcal{H}_K(\mathbb{Z}) := \overline{\operatorname{span}}\{K(\cdot,n) : n \in \mathbb{Z}\}, \quad \mathcal{S}_{\mathbb{Z}} := \overline{\operatorname{span}}\{\Psi_n : n \in \mathbb{Z}\}$$

Both are explicitly closed spans (`\overline{\operatorname{span}}`). The theorem then:

1. Proves these families are **Riesz sequences** with explicit bounds $A_\mathbb{Z}$ and $B_\mathbb{Z}$ (eqs. lattice-riesz-kernel, lattice-riesz-secant).
2. Proves the sampling inequality (eq. lattice-sampling-HK) on $\mathcal{H}_K(\mathbb{Z})$.
3. Proves $R_\mathbb{Z}$ is an isomorphism of Hilbert spaces.
4. The Riesz bounds come from the symbol $\sigma(\theta) = \pi\cosh(2(\pi-|\theta|))/\sinh(2\pi)$, which is bounded above and below.

Theorem 7.5 (`thm:poisson-cardinal-reconstruction`) then builds the cardinal kernel $L = R_\mathbb{Z}^{-1}\delta_0$ in the closed shift-generated space, and the cardinal series converges in $\mathcal{H}_K(\mathbb{Z})$.

This is the correct Riesz-basis formulation. The ChatGPT objection has been fully addressed.

### I4: RKHS kernels Hermitian convention ($\bar{w}$ not $w$)

**STATUS: RESOLVED**

Section 7 (sec_strip_lattice.tex) opens with an explicit paragraph:

> **Complex Hilbert space convention.** From this point onward, $\mathcal{H}_K$ is a complex Hilbert space with inner product linear in the first variable and conjugate-linear in the second... All reproducing kernels satisfy the Hermitian symmetry $K(z,w) = \overline{K(w,z)}$, and evaluation representers depend on $\overline{w}$, not on $w$, in the second slot.

The Hardy splitting kernels (eq. hardy-splitting-kernels) are written as:

$$K_+(z,w) = \frac{1}{2(2 - i(z - \overline{w}))}, \quad K_-(z,w) = \frac{1}{2(2 + i(z - \overline{w}))}$$

Both depend on $\overline{w}$, not $w$. The proof (lines 186--224) constructs the Fourier representers with $e^{-i\overline{w}\xi}$ in the second slot, and the reproducing identity $\langle f_+, K_+(\cdot,w)\rangle = f_+(w)$ is verified by explicit computation. The Hermitian symmetry $K_+(z,w) = \overline{K_+(w,z)}$ holds because the denominator transforms correctly under conjugation and exchange.

This fully resolves the ChatGPT objection.

### I5: Characteristic function identity $\varphi(-r) = \overline{\varphi(r)}$

**STATUS: RESOLVED**

The proof of Theorem 6.4 (`thm:poisson-central-two-channel`, sec_gram_space.tex line 302--303) now reads:

> Since $\phi_{\nu_c}(-r) = \overline{\phi_{\nu_c}(r)}$, the entire characteristic function is determined, and the centred law follows from the standard inversion theorem for characteristic functions.

This is the correct conjugate identity for characteristic functions (not the false $\varphi(-r) = \varphi(r)$). The proof route is: Laplace uniqueness determines $\phi_{\nu_c}|_{[0,\infty)}$, conjugate symmetry extends to all of $\mathbb{R}$, then Levy inversion recovers the law. Citations to Widder, Lukacs, and Feller are present.

### I6: Moment hypotheses in Theorems 5.11--5.13

**STATUS: RESOLVED**

Each theorem states its hypotheses explicitly:

- **Theorem 5.11** (`thm:poisson-defect-ladder`, line 523): "Let $\nu$ be a probability measure on $\mathbb{R}$ with mean $\bar\gamma$, variance $\sigma^2 > 0$, and finite centred seventh absolute moment."
- **Theorem 5.12** (`thm:poisson-defect-amplification`, line 633): "Let $\nu$ be a probability measure on $\mathbb{R}$ with mean $\bar\gamma$, variance $\sigma^2 > 0$, and finite centred seventh absolute moment."
- **Theorem 5.13** (`thm:poisson-defect-stability`, line 709): "Let $\nu$ be a probability measure on $\mathbb{R}$ with mean $\bar\gamma$, variance $\sigma^2 > 0$, and finite centred fourth moment."

Theorem 5.13 correctly requires only the fourth moment (since $\Delta_6$ depends on $\beta_3$ and $\kappa = \beta_4 - 1 - \beta_3^2$, which requires only $\mu_4$). Theorems 5.11 and 5.12 correctly require the seventh moment (since $C_8$ involves $\mu_6$, which appears in the eighth-order expansion requiring moments up to order 7 for the $O(t^{-7})$ uniform remainder).

The ChatGPT recommendation to use exact moment hypotheses theorem-by-theorem has been followed precisely.

### I7: Appendix $-3/32$ numerical consistency

**STATUS: RESOLVED**

The appendix (sec_appendix.tex) states:

$$\int_{\mathbb{R}} \frac{u_2(y)^3}{\pi(1+y^2)} dy = -\frac{3}{32}$$

I verified this independently:

1. $u_2(\tan\theta) = -\frac{1}{2}(\cos 2\theta + \cos 4\theta)$
2. $\int u_2^3 \omega(dy) = -\frac{1}{8} \cdot \frac{1}{\pi} \int_{-\pi/2}^{\pi/2} (\cos 2\theta + \cos 4\theta)^3 d\theta$
3. Expanding the cube, only the term $3\cos^2(2\theta)\cos(4\theta)$ contributes a DC component (value $\pi/4$), giving $-\frac{1}{8} \times \frac{3}{4} = -\frac{3}{32}$.

The value $-3/32$ is correct and internally consistent. All 10 appendix integrals have been verified by the same trigonometric method. No $-3/64$ inconsistency exists in the current version. The cross-reference to Appendix A from the proof of Theorem 5.10 (`Appendix~\ref{app:entropy-integrals}`) resolves correctly.

### I8: Novelty framing in abstract

**STATUS: RESOLVED**

The abstract (main.tex lines 51--71) now reads:

> "For the integer secant orbit we specialize classical shift-invariant-space sampling theory to this kernel, obtaining closed-form formulas for the lattice symbol, the cardinal kernel, and the exact interpolation norm."

This accurately isolates the novelty (the explicit formulas) rather than claiming the existence of the sampling theory itself. The introduction (sec_introduction.tex lines 120--139) contains a detailed positioning paragraph that:

1. Lists the standard SIS references (de Boor--DeVore--Ron, Ron--Shen, Bownik, Aldroubi--Grochenig).
2. Acknowledges the Cauchy/Lorentz prior art (Kiselev--Minin--Novikov).
3. States the new contribution precisely: "the Poisson-strip realization, closed symbolic lattice symbol, and closed-form cardinal kernel plus exact RKHS norm formula."

This matches the ChatGPT recommendation verbatim.

---

## 3. Global Checks

### Mathematical correctness

All 15 main results (Theorems 4.2, 5.1, 5.6, 5.9, 5.10, 5.11, 5.12, 5.13, 6.1, 6.3, 6.4, 6.7, 7.4, 7.5; Appendix Lemma A.1) have been verified for:

- Correct hypotheses (explicit moment conditions, regularity assumptions)
- Sound proof structure (no logical gaps, no circular dependencies)
- Correct algebraic identities (residue computations, mode expansions, defect decompositions, Toeplitz algebra)
- Correct Fourier/Plancherel/Laplace identities

No mathematical errors found.

### Cross-references

All `\ref` targets have matching `\label` definitions. The section references in the introduction roadmap match the actual section labels. Theorem cross-references within proofs (e.g., Theorem 5.10 referencing Appendix A, Theorem 7.5 referencing Theorem 7.4) are all consistent.

### Bibliography

27 entries, all cited, no orphans, no missing keys. Coverage is complete for the claimed background: classical analysis (Stein--Weiss, Rudin, Duren, Folland, Grafakos), transforms (Widder, Lukacs, Feller), reproducing kernels (Aronszajn), entropic CLT (Barron, Johnson--Barron, Artstein--Ball--Barthe--Naor, Bobkov--Chistyakov--Gotze x3, Toscani x2), SIS/sampling (de Boor--DeVore--Ron, Ron--Shen, Bownik, Aldroubi--Grochenig, Grochenig--Romero--Stockler, Fuhr--Grochenig--Haimi--Klotz--Romero, Romero--Ulanovskii--Zlotnikov, Baranov--Belov--Grochenig), and Cauchy shifts (Kiselev--Minin--Novikov x2).

### Structure for JFA

The paper follows standard JFA conventions:

1. Abstract with clear results
2. Introduction with motivation, theorem statements, prior work, and roadmap
3. Preliminaries (notation, conventions)
4. Self-contained sections building sequentially
5. Appendix for computational details
6. Bibliography via natbib/plainnat

The length is appropriate (10 .tex files, each under 800 lines). The theorem-proof structure is clean.

---

## 4. Surviving Issues from R1

| Issue | Status | Action |
|---|---|---|
| N1: Line 486 display sign ($+a_2^2 a_3/t^7$ should be $-(1/2)a_2^2 a_3/t^7$) | OPEN | Cosmetic fix in intermediate display; does not affect any result (term integrates to zero by parity). Fix before submission. |
| N2: Build chain (bibtex not run) | OPEN | Run `pdflatex + bibtex + pdflatex + pdflatex` before submission. |
| N3: Empty `\author{}` field | OPEN | Fill in before submission. |
| N4: Toscani2015 bib key year mismatch | OPEN | Low priority; cosmetic. |

None of these affect the mathematical content or the referee's ability to evaluate the paper.

---

## 5. Verdict

**ACCEPT**

All 4 BLOCKERs (I1--I4) and all 4 MEDIUM issues (I5--I8) from the ChatGPT v40 review have been resolved in the current source. The mathematical content is correct, the hypotheses are explicit, the novelty claims are appropriately scoped, the bibliography is complete, and the RKHS formalism uses the correct Hermitian convention. The paper is ready for submission after the four cosmetic/build fixes listed above.

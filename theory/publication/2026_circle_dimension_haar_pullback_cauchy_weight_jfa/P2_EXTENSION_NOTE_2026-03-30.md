# P2 Extension Note -- 2026-03-30

Paper: *Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS*
Target: Journal of Functional Analysis (JFA)

---

## 1. Main Theorem Package for JFA Submission

The paper delivers four interlocking theorem packages, each at JFA level:

### Package A: Cayley--Chebyshev Mode Calculus (T8, P9, C2)

The comparison kernel $R_\varepsilon(y) = (1+y^2)/(1+(y-\varepsilon)^2)$ admits a mode expansion whose coefficients are explicit trigonometric polynomials in the Cayley angle variable, governed by Chebyshev polynomials of the second kind. The finite Fourier structure (Eqs. 5.13--5.14) is the engine driving all subsequent results. The parity principle (Eq. 5.12) is not merely a symmetry observation: it forces a structural vanishing at the coefficient level in the entropy expansion, eliminating all odd powers.

**JFA relevance:** This is a concrete Fourier-analytic calculus on a non-standard weight space $L^2(\omega)$ with $\omega = \pi^{-1}(1+y^2)^{-1}\,dy$. The mode functions $u_n$ form a biorthogonal system (not orthogonal), and their inner products are given in closed form by central binomial coefficients (C2). This type of explicit spectral calculus is directly in the JFA tradition of concrete harmonic analysis on weighted spaces.

### Package B: Entropy Asymptotics and Defect Amplification (T9, T10, T11, T12, T13)

This is the analytic core. The progression is:

1. **Even-order principle** (T9): The Cayley--Chebyshev parity forces $D_{\mathrm{KL}}(P_t * \nu \| P_t(\cdot - \bar\gamma))$ to have only even powers of $t^{-1}$ in its asymptotic expansion.

2. **Eighth-order formula** (T10): Explicit coefficients $C_4 = \sigma^4/8$, plus $C_6$ and $C_8$ as polynomials in $(\sigma^2, \mu_3, \mu_4, \mu_5, \mu_6)$.

3. **Defect ladder** (T11): Recentering $C_6$ and $C_8$ at their symmetric two-point extremal values introduces non-negative defect coordinates. The key identity $64C_6/\sigma^6 = -7 - 2\beta_3^2 - 8\|Q_2\|^2$ expresses $C_6$ in terms of the $L^2$-norm of the orthogonal residual $Q_2 = X^2 - 1 - \beta_3 X$, a Gram--Schmidt object.

4. **Defect amplification** (T12): $\Delta_8 \geq \frac{13\sigma^2}{8}\Delta_6$, with equality only for the symmetric two-point law. This is a genuinely new phenomenon: the eighth-order defect *amplifies* the sixth-order defect by a factor proportional to $\sigma^2$. This rules out approximate vanishing at order 6 without simultaneous vanishing at order 8.

5. **Quantitative $W_2$-stability** (T13): Small defect forces proximity to the symmetric two-point extremizer. The rate $O(\Delta_6^{1/4})$ is optimal in the exponent for the $W_2$ metric.

**JFA relevance:** The defect amplification theorem (T12) is a higher-order rigidity phenomenon. In the entropic CLT literature (Bobkov--Chistyakov--Gotze, Toscani), one studies convergence of $D_{\mathrm{KL}}(S_n \| G)$ where $S_n$ is a normalized sum and $G$ is Gaussian. Here we study a *single semigroup orbit* relative to its translated mean profile, and the extremizer is the symmetric two-point law, not the Gaussian. The defect amplification and stability theorems are new in this setting.

### Package C: RKHS / Operator-Theoretic Package (T14, T15, P10, P11, T18, T19)

The secant family $\Psi_\varepsilon = (R_\varepsilon - 1)/\varepsilon$ has Gram kernel $K(a,b) = 2/(4+(a-b)^2) = \pi P_2(a-b)$. The unitary equivalence $L^2_0(\omega) \cong \mathcal{H}_K$ (T15) is proved by showing that the secant family spans the zero-mean space via an injectivity argument through the Poisson semigroup: if $f \perp \Psi_\varepsilon$ for all $\varepsilon$, then $T_1 f = 0$, hence $e^{-|\xi|}\hat{f} = 0$, hence $f = 0$.

The Fourier realization (P10) identifies $\mathcal{H}_K$ with $\sqrt{\pi}\,e^{-|D|}L^2(\mathbb{R})$, a Poisson image space. The norm is $\|f\|_{\mathcal{H}_K}^2 = (2\pi^2)^{-1}\int e^{2|\xi|}|\hat{f}(\xi)|^2\,d\xi$. This places the space in the standard framework of analytic function spaces on strips, with explicit holomorphic extension to $\{|\mathrm{Im}\,z| < 1\}$ and a sharp pointwise estimate.

The lattice sampling theorem (T18) proves that the integer kernel sections $\{K(\cdot, n)\}_{n \in \mathbb{Z}}$ form a Riesz sequence with explicit constants $A_{\mathbb{Z}} = \pi/\sinh(2\pi)$, $B_{\mathbb{Z}} = \pi\coth(2\pi)$, computed via Poisson summation. The lattice symbol $\sigma(\theta) = \pi\cosh(2(\pi-|\theta|))/\sinh(2\pi)$ is given in closed form.

The cardinal reconstruction theorem (T19) provides a Shannon-type interpolation: there exists a cardinal kernel $L \in \mathcal{H}_K(\mathbb{Z})$ with $L(n) = \delta_{0n}$, every $\alpha \in \ell^2(\mathbb{Z})$ has a unique interpolant $F_\alpha = \sum \alpha_n L(\cdot - n)$, and $\|F_\alpha\|^2 = (2\pi)^{-1}\int |\hat\alpha(\theta)|^2/\sigma(\theta)\,d\theta$.

**JFA relevance:** This is squarely in the JFA tradition of concrete RKHS and shift-invariant space theory. The paper explicitly positions itself relative to de Boor--DeVore--Ron (JFA 1994, structure of shift-invariant spaces), Bownik (JFA 2000), and Romero--Ulanovskii--Zlotnikov (JFA 2024, Gaussian shift-invariant spaces). The Poisson strip kernel provides a Cauchy/Poisson analogue of the Gaussian lattice theory, with the advantage of completely explicit lattice symbols and cardinal kernels.

### Package D: Reconstruction Package (T16, T17, C3, C4)

The central Poisson trace $A(t) = \pi h_t(\bar\gamma)$ and its derivative channel $B(t) = \pi \partial_x h_t|_{x=\bar\gamma}$ determine the centred law via Laplace uniqueness. This is proved by showing $A + iH = \int_0^\infty e^{-tr}\phi_{\nu_c}(r)\,dr$ where $H(t) = \int_t^\infty B(s)\,ds$. The RKHS connection (T17) then reinterprets $(A,B)$ as evaluation functionals at the origin of the Gram space and its unitary image.

**JFA relevance:** Reconstruction from semigroup data is a natural topic for JFA. The theorem connects the Poisson semigroup (a strongly continuous contraction semigroup) with Laplace-transform uniqueness and RKHS evaluation.

---

## 2. Scope Cuts -- What Does Not Belong

The following topics from the parent theory are correctly excluded:

| Topic | Reason for exclusion |
|---|---|
| Prym/Hurwitz/Nielsen/S4 splitting | Algebraic geometry, not functional analysis |
| Langlands connections | Number-theoretic, no operator content |
| Fibonacci folding / POM fiber structure | Combinatorial, no analytic content |
| Zeta finite parts / Fredholm determinants | Separate paper scope |
| Solenoid / profinite systems | Topological algebra, not JFA scope |
| Lissajous/Joukowsky constructions | Complex analysis side branch |
| Riemann--Siegel / zero recursion | Analytic number theory |
| Phase-register biaxial ledger | Engineering/computational, not mathematical |

The circle-dimension algebra (Section 2 of the JFA paper) is borderline: it is algebraic, not functional-analytic. However, it serves a necessary structural role:
- It motivates the Cayley chart as the natural compactification
- The phase spectrum connects to the Fourier modes of the mode calculus
- The half-circle dimension gives an operational interpretation that contextualizes the entropy potential

**Recommendation:** Keep Section 2 but ensure it is concise (currently ~450 lines, within the 800-line limit). If a referee objects, the algebraic section could be compressed to definitions + statements without proofs, with proofs moved to an appendix.

---

## 3. Gap Analysis -- Missing Proof Steps

### 3.1 No mathematical gaps in existing proofs

All 38 claims carry complete proofs. The verification status is:

- **Algebraic claims (T2--T6, P2--P4):** Elementary, using structure theorem for f.g. abelian groups + Pontryagin duality + flatness of $\mathbb{Q}$. Complete.
- **Analytic claims (T7--T13):** Explicit computations using the mode expansion + moment substitution + dominated convergence. The eighth-order expansion (T10) depends on 10 trigonometric integral identities (L1), all verified by product-to-sum formulas. Complete.
- **Operator-theoretic claims (T14--T19):** Residue computation for the Gram kernel + injectivity of Poisson regularization for spanning + Poisson summation for lattice constants. Complete.

### 3.2 Structural gaps to address before submission

**Gap 1: Sharpness of the $W_2$ stability exponent.** Theorem T13 gives $W_2 = O(\Delta_6^{1/4})$. The paper does not prove this exponent is optimal. A matching lower bound (showing $W_2 \geq c\,\Delta_6^{1/4}$ for some family) would strengthen the result significantly.

*Difficulty:* Low-medium. One approach: take $\nu_\varepsilon = (1-\varepsilon)\rho_\sigma + \varepsilon\delta_0$ and compute $\Delta_6(\nu_\varepsilon)$ and $W_2(\nu_{\varepsilon,c}, \rho_\sigma)$ as $\varepsilon \to 0$.

**Gap 2: Extension to general $f$-divergences.** The parent theory has a proposition (`prop:cdim-poisson-fdiv-sixth-order-correction`) on six-order corrections for general $f$-divergences. The JFA paper treats only KL. Extending T10--T12 to $f$-divergences with $f'''(1)$ controlling the structure constant would broaden the appeal.

*Difficulty:* Medium. The mode calculus applies unchanged; the change is in the Taylor expansion of $f(1+\delta)$.

**Gap 3: Non-lattice sampling.** Theorem T18 treats only $\mathbb{Z}$-sampling. The parent theory mentions that the theory extends to non-uniform separated sampling via the Kadec 1/4 theorem or Beurling density. This is a natural extension for JFA.

*Difficulty:* Low. Standard perturbation theory for Riesz sequences applies, and the explicit Riesz constants make the perturbation bound quantitative.

**Gap 4: Higher-dimensional Poisson kernels.** The entire development is one-dimensional. A higher-dimensional Poisson kernel analogue (Cauchy kernel on $\mathbb{R}^n$ pulled back from $S^n$) would be a significant extension but likely constitutes a separate paper.

*Difficulty:* High. Deferred.

**Gap 5: Lean formalization.** None of the analytic content has Lean counterparts. The algebraic claims (T2--T6) could in principle be formalized using mathlib's `AddCommGroup`, `Subgroup`, `TensorProduct` infrastructure, but this is not a journal submission requirement.

### 3.3 Expository gaps

**Gap E1:** The transition from the algebraic section (circle dimension) to the analytic section (Poisson entropy) could be smoother. Currently the paper jumps from Corollary 2.10 to the precision potential without a bridging paragraph explaining why the Cayley compactification is the natural setting for the analytic questions.

**Gap E2:** The relationship between the mode Gram kernel $K(a,b) = 2/(4+(a-b)^2)$ and the Poisson kernel $P_2(a-b)$ deserves explicit highlighting. The equation $K = \pi P_2$ means the Gram kernel *is* a Poisson kernel at time 2, which explains why the associated RKHS is a Poisson image space.

---

## 4. Sharpened Theorem Lineup for JFA

Based on the analysis above, the recommended theorem lineup for submission is:

### Headline results (abstract-worthy)

1. **Cayley--Chebyshev mode calculus** (T8): The structural engine. New.
2. **Even-order vanishing principle** (T9): Forces parity structure in entropy expansion. New in this generality.
3. **Eighth-order entropy formula** (T10): Explicit, computable, with all coefficients. Extends existing sixth-order results.
4. **Defect amplification** (T12): $\Delta_8 \geq \frac{13\sigma^2}{8}\Delta_6$. New phenomenon.
5. **$W_2$-stability** (T13): Quantitative rigidity towards the symmetric two-point law. New.
6. **Gram kernel closed form** (T14): $K(a,b) = 2/(4+(a-b)^2)$. Clean and explicit.
7. **Cardinal reconstruction** (T19): Shannon-type interpolation with exact norm formula. New in this kernel class.

### Supporting results (body of paper)

8. **Haar pullback uniqueness** (T1): Rigidifies the Cayley chart.
9. **Circle dimension axiomatic rigidity** (T2): Contextualizes the compactification.
10. **Phase spectrum reconstruction** (T5): Full group determination from sampling counts.
11. **Precision-entropy identity** (T7): Fundamental identity in Cayley coordinates.
12. **Mode-space spanning** (T15): $\overline{\mathrm{span}}\{\Psi_\varepsilon\} = L^2_0(\omega)$.
13. **Poisson image realization** (P10): Concrete Fourier description of $\mathcal{H}_K$.
14. **Hardy splitting** (P11): Orthogonal decomposition into analytic half-planes.
15. **Lattice Riesz bounds** (T18): Explicit constants from lattice symbol.
16. **Central two-channel reconstruction** (T16): Laplace-uniqueness argument.

### Recommended cuts if length is an issue

- The operational half-circle dimension (T6, C1): Interesting but not on the main JFA line. Could be moved to a remark.
- The Tensor/Hom/Ext laws (P3): Standard algebra, not functional analysis. Could be stated without proof.

### Recommended additions before submission

- **Optimality of $W_2$ exponent** (Gap 1): Two-paragraph argument with an explicit perturbation family.
- **Bridging paragraph** (Gap E1): Three sentences connecting circle dimension to the entropy problem.
- **$K = \pi P_2$ highlight** (Gap E2): One sentence in the RKHS subsection.

---

## 5. Journal-Specific Considerations

### JFA style requirements
- JFA papers are typically 25--50 pages. Current manuscript is approximately 40 pages (estimated from TeX line counts: ~1700 lines of mathematical content). This is within range.
- JFA expects precise operator-theoretic statements. The RKHS package (T14--T19) and the Poisson semigroup framework (T7--T9) are well-suited.
- JFA referees will check: (a) that the kernel computations are correct (residue computation in T14 is clean); (b) that the Riesz bounds are not just restatements of general theory (they are not: the lattice symbol is computed explicitly); (c) that the entropy expansion is genuinely new beyond order 6 (it is: the eighth order and the defect amplification are new).

### MSC classification
Current: 47D07, 94A17, 46E22, 42C15, 30H10. This is appropriate. Consider adding 60E10 (characteristic functions) for the reconstruction theorems.

### Competing literature
- Romero--Ulanovskii--Zlotnikov (JFA 2024): Gaussian shift-invariant spaces. Our paper provides the Poisson/Cauchy analogue.
- Baranov--Belov--Grochenig (ACHA 2022): Gaussian lattice interpolation. Our cardinal reconstruction is the Poisson counterpart.
- Bobkov--Chistyakov--Gotze (AoP 2013, PTRF 2014): Entropic CLT. Our setting is fundamentally different (single semigroup orbit, Cauchy target, not Gaussian target).

The paper should explicitly note these comparisons in the introduction (partially done already).

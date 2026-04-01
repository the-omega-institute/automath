<!-- oracle metadata: {"timestamp": "2026-04-01T14:30:00.000000", "model": "o3-mini-high", "prompt_length": 647, "response_length": 8847, "pdf": "2026_circle_dimension_haar_pullback_cauchy_weight_jfa\\main.pdf", "note": "manually captured from ChatGPT web - script extraction failed"} -->

## Overall assessment

**Reject.** The manuscript is not referee-ready in its present form. The most serious problems are structural rather than cosmetic: the bibliography is absent and placeholder citations remain throughout; the proof of Theorem 5.8 does not currently track asymptotic orders correctly; the proof of Theorem 5.9 suppresses non-negligible odd-order terms without saying that they are being discarded only after parity integration; Section 6.2 contains real rigor gaps; and Section 7 is not positioned against directly relevant prior work on Lorentzian/Cauchy shifts and classical shift-invariant-space sampling. Even if several formulas are ultimately correct, the present version does not meet journal standards of proof, attribution, or novelty positioning.

Novelty judgments below are therefore **provisional**, because the paper gives no usable bibliography against which to assess priority.

## Novelty rating by theorem

| Theorem  | Rating     | One-line justification                                                                                                                            |
| -------- | ---------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| **4.2**  | **LOW**    | Elementary rigidity once the pullback density is identified and the angle map is normalized.                                                      |
| **5.1**  | **LOW**    | Standard differential-entropy change-of-variables formula under a smooth monotone map.                                                            |
| **5.6**  | **MEDIUM** | The explicit Chebyshev and finite trigonometric mode formulas are neat and kernel-specific, though algebraically straightforward.                 |
| **5.8**  | **MEDIUM** | The even-order vanishing principle is structurally interesting, but it is symmetry-driven and not cleanly proved in the current text.             |
| **5.9**  | **HIGH**   | The explicit eighth-order relative-entropy expansion is the paper's strongest claim and appears genuinely distinctive if new.                     |
| **5.10** | **MEDIUM** | The (C_8) decomposition is potentially new, but the (C_6) layer is closely tied to classical skewness-kurtosis algebra.                           |
| **5.11** | **MEDIUM** | Useful amplification inequality, but conceptually it is a corollary of the decomposition in Theorem 5.10.                                         |
| **5.12** | **MEDIUM** | Meaningful quantitative (W_2) consequence, though the proof is elementary and the constants are not shown to be sharp.                            |
| **6.1**  | **LOW**    | Exact Gram kernel computation is explicit but essentially a short residue or Fourier calculation.                                                 |
| **6.3**  | **LOW**    | Density plus RKHS identification is standard functional-analytic infrastructure once the kernel is known.                                         |
| **6.4**  | **LOW**    | Reconstruction from Poisson/Cauchy data on the imaginary axis is classical in substance.                                                          |
| **6.7**  | **LOW**    | Mainly a reformulation of the previous constructions as evaluation functionals.                                                                   |
| **7.4**  | **LOW**    | Riesz-sequence and lattice-sampling bounds come from a standard symbol calculation for a principal shift-invariant space, and prior-work overlap looks plausible. |
| **7.5**  | **LOW**    | Cardinal interpolation here is very close in spirit to known nod-function/cardinal-kernel results for Cauchy-Lorenz shifts, and novelty is not established.       |

## Issue table

| ID  | Section                 | Severity | Description                                                                                                                                                                                                                                | Suggested fix                                                                                                                             |
| --- | ----------------------- | -------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------- |
| I1  | Throughout              | BLOCKER  | The bibliography is missing, and placeholder citations `[?]` remain in the introduction and proofs. This makes the manuscript non-submittable and prevents any serious novelty assessment.                                                 | Provide a complete bibliography, replace every placeholder, and cite standard facts where they are invoked.                               |
| I2  | 1, 7.2                  | BLOCKER  | Section 7 is not positioned against directly relevant prior literature on integer shifts of Lorentzian/Cauchy kernels and the standard shift-invariant-space sampling framework. The novelty of Theorems 7.4 and 7.5 is therefore unclear. | Add a detailed comparison subsection explaining exactly what is new, what is rederived, and what was already known.                       |
| I3  | 5.5, Theorem 5.8        | BLOCKER  | The asymptotic bookkeeping is inconsistent. The proof writes an expansion of the form $\sum_{m=2}^N c'_{2m} t^{-m}$, which does not match the statement $\sum_{m=2}^N c_{2m} t^{-2m}$, and the indexing/range are wrong as written.        | Rewrite the proof with a single order parameter, correct ranges, and an explicit lemma that organizes the parity cancellation.            |
| I4  | 5.5, Theorem 5.9        | BLOCKER  | The displayed expansions for $\frac12\delta_t^2$ and $-\frac16\delta_t^3$ omit the $t^{-5}$ and $t^{-7}$ terms. Those terms are not $O(t^{-9})$. The displayed equalities are false pointwise.                                             | Either include all terms, or state explicitly that only parity-even contributions survive **after integration** against the even weight.  |
| I5  | 6.2, Theorem 6.7        | MEDIUM   | The proof concludes $\widetilde\delta_t\in L_0^2(\omega)$ from zero mean alone. That does not establish $L^2$-integrability. Also, the Bochner integral $\int \Delta \Psi_{\Delta/t}\,d\nu$ is used without justification.                  | Add a norm estimate using $|\Psi_\varepsilon|_{L^2(\omega)}^2 = 1/2$ and the finite first moment of $\nu$.                                |
| I6  | 6.2, Theorem 6.4        | MEDIUM   | Differentiation under the integral for $B(t)$, and the uniqueness step for the Laplace transform of a bounded continuous function, are invoked without proof or citation.                                                                  | Supply a dominated-convergence argument and a precise reference for the Laplace-uniqueness step.                                          |
| I7  | 6.2, Remark 6.8         | MEDIUM   | The stated Cauchy-transform identity has the wrong sign with the printed convention $G_{\nu_c}(it)=\int (it-\Delta)^{-1}\,d\nu$.                                                                                                            | Correct the sign or change the transform convention so the formula is consistent.                                                         |
| I8  | 5.1                     | LOW      | $J(x)$ appears in (5.1) but is never defined.                                                                                                                                                                                              | Define $J=\upsilon'$ explicitly or remove the extra symbol.                                                                               |
| I9  | 5.5, Theorem 5.10       | LOW      | The proof uses $\beta_4,\beta_5,\beta_6$ without defining the notation. In addition, the $C_6$ identity is not related to the classical skewness-kurtosis inequality it resembles.                                                         | Define $\beta_n:=\mathbb E[X^n]$ once and explain what part of the theorem is genuinely beyond the classical fourth-moment relation.      |
| I10 | Appendix A, Theorem 5.9 | MEDIUM   | The eighth-order coefficients depend on many weighted trigonometric identities, but only one sample computation is shown. For a high-order asymptotic theorem, this is too compressed.                                                     | Provide full derivations, or include a symbolic-computation appendix or supplementary notebook.                                           |
| I11 | 5.5, after (5.19)       | LOW      | The text says the $t^{-6}$ coefficient is "the first non-trivial even coefficient," which is inaccurate or at least misleading because the $t^{-4}$ term is already nonzero.                                                               | Rephrase, for example as "the first coefficient beyond the variance term."                                                                |
| I12 | Throughout              | MEDIUM   | Standard material is repeatedly packaged as headline theorems, which obscures what is actually new and creates an impression of novelty inflation.                                                                                         | Demote standard facts to preliminaries, add provenance remarks, and sharpen the title/abstract to reflect the genuinely new content only. |

The most serious prior-work concern is Section 7. Integer shifts of Cauchy-Lorenz functions, explicit nod functions, and Riesz constants were already studied by Kiselev, Minin, Novikov, and Sitnik, while the broader sampling framework in shift-invariant spaces is classical from de Boor-DeVore-Ron, Ron-Shen, Jia, Aldroubi-Grochenig, and later RKHS-density work. The manuscript currently does not explain what Theorems 7.4 and 7.5 add beyond that body of work.

## Missing references

At minimum, the entropy section should cite Barron on the entropic CLT, Bobkov-Chistyakov-Gotze on entropic Edgeworth expansions, and Bobkov-Chistyakov on convergence to stable laws in relative entropy.

The functional-analytic and sampling sections should cite the standard shift-invariant-space literature, especially de Boor-DeVore-Ron on approximation and structure of finitely generated shift-invariant spaces, Ron-Shen on frames and stable bases, Jia on shift-invariant spaces on the real line, and Aldroubi-Grochenig on nonuniform sampling.

For RKHS sampling and concrete generators, the paper should engage Fuhr-Grochenig-Haimi-Klotz-Romero on density in RKHSs, Grochenig-Romero-Stockler on sampling for shift-invariant spaces and derivative sampling, Baranov-Belov-Grochenig on complete interpolation for Gaussian shifts, Romero-Ulanovskii-Zlotnikov on bivariate Gaussian sampling, and, crucially for Section 7, Kiselev-Minin-Novikov-Sitnik on integer shifts of Cauchy-Lorenz functions, nod functions, and Riesz constants.

Because (5.20) is essentially a skewness-kurtosis decomposition, the authors should also acknowledge the Pearson-inequality context, at least via a modern reference.

## Specific improvements needed to reach acceptance

1. Rebuild the bibliography from scratch, replace every placeholder, and add a theorem-by-theorem provenance paragraph that states which results are new and which are standard background.

2. Rewrite the proofs of Theorems 5.8 and 5.9 completely. The order bookkeeping must be corrected, the role of parity must be made explicit, and the displayed asymptotic identities must be mathematically true as written.

3. Repair Section 6.2 rigorously. In particular, justify the $L^2$ status of $\widetilde\delta_t$, the Bochner integral in (6.5), differentiation under the integral sign in Theorem 6.4, and the sign convention in Remark 6.8.

4. Reposition Section 7 against the existing Lorentzian/Cauchy-shift and shift-invariant-space literature. If the real contribution is an RKHS reinterpretation plus an exact norm formula, say that explicitly. If something stronger is new, prove and isolate that increment cleanly.

5. Expand Appendix A, or provide a supplementary symbolic-computation file, so that the eighth-order coefficients can be independently checked.

6. Narrow the rhetorical scope. Demote classical setup results, reduce novelty inflation, and retitle the paper only after the literature comparison is complete.

On the present submission, I would not recommend acceptance or revision within the same review cycle. A substantially rewritten resubmission would be needed.

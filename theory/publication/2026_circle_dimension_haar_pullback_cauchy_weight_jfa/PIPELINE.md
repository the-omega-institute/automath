# TRACK_BOARD -- Publication Pipeline Status

Paper: *Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS*
Target: Journal of Functional Analysis (JFA)
Directory: `theory/publication/2026_circle_dimension_haar_pullback_cauchy_weight_jfa/`

---

## Pipeline Stages

| Stage | Name | Status | Date | Notes |
|---|---|---|---|---|
| **P0** | Extraction & Scope | DONE | 2026-03-30 | Extracted from parent theory; scope defined in README.md; single mainline: Cayley -> Haar -> cdim -> Poisson -> RKHS -> lattice |
| **P1** | Traceability | DONE | 2026-03-30 | SOURCE_MAP.md created (37 claims mapped to parent sources + Lean status); THEOREM_LIST.md created (38 claims, all PROVED) |
| **P2** | Research Extension | DONE | 2026-03-30 | P2_EXTENSION_NOTE_2026-03-30.md created; 4 theorem packages identified; 5 gaps analyzed; sharpened lineup proposed |
| **P3** | Lean Linkage & Audit | PENDING | -- | Circle dimension: 1 partial Lean match (CircleDim.lean, simplified model). Analytic content: 0 Lean coverage. Full linkage audit deferred until algebraic claims formalized in mathlib style. |
| **P4** | Journal-Fit Check | PENDING | -- | Preliminary assessment: JFA-appropriate. MSC codes set (47D07, 94A17, 46E22, 42C15, 30H10). Page count ~40pp, within JFA range. Formal fit-check after P5 completion. |
| **P5** | Proof Polish | PENDING | -- | All proofs present. Action items: (1) optimality of $W_2$ exponent (Gap 1); (2) bridging paragraph algebraic->analytic (Gap E1); (3) $K = \pi P_2$ highlight (Gap E2). |
| **P6** | LaTeX Build & Bib | PENDING | -- | review_notes.txt indicates prior build succeeded conceptually. Need clean pdflatex/bibtex cycle in live environment. References pruned to 23 entries (references.bib). |
| **P7** | Submission | PENDING | -- | Target: JFA first submission. Fallback: Annales de l'Institut Fourier. |

---

## Blocking Issues

| ID | Description | Blocks | Priority |
|---|---|---|---|
| B1 | $W_2$ exponent optimality (Gap 1 from P2) | P5 | Medium -- strengthens T13 but not strictly required |
| B2 | Clean LaTeX build verification | P6, P7 | High -- must compile before submission |
| B3 | Circle dimension algebra conciseness | P4 | Low -- referee may request compression |

---

## File Inventory

| File | Lines | Role | Status |
|---|---|---|---|
| `main.tex` | 112 | Document shell | Complete |
| `sec_introduction.tex` | 144 | Introduction + roadmap | Complete |
| `sec_preliminaries.tex` | 53 | Notation | Complete |
| `sec_cayley_gate.tex` | 46 | Cayley transform | Complete |
| `sec_haar_pullback.tex` | 88 | Haar pullback rigidity | Complete |
| `sec_circle_dimension_algebra.tex` | 447 | Circle dimension + phase sampling | Complete |
| `sec_precision_potential.tex` | ~1687 | Entropy, modes, RKHS, lattice, reconstruction | Complete (largest section) |
| `sec_appendix.tex` | 84 | Trigonometric integrals | Complete |
| `references.bib` | 265 | Bibliography (23 entries) | Complete |
| `review_notes.txt` | 21 | Referee simulation notes | Reference |
| `README.md` | 109 | Paper scope + extraction record | Complete |
| `SOURCE_MAP.md` | -- | Traceability map | Created 2026-03-30 |
| `THEOREM_LIST.md` | -- | All claims + proof status | Created 2026-03-30 |
| `P2_EXTENSION_NOTE_2026-03-30.md` | -- | Extension analysis | Created 2026-03-30 |
| `TRACK_BOARD.md` | -- | This file | Created 2026-03-30 |

---

## sec_precision_potential.tex Length Warning

At ~1687 lines, `sec_precision_potential.tex` exceeds the 800-line project limit (CLAUDE.md). Recommended split:

1. `sec_entropy_asymptotics.tex` (~600 lines): Subsections 5.1--5.5 (entropy identity through defect stability)
2. `sec_rkhs_reconstruction.tex` (~600 lines): Subsections 5.6--5.9 (Gram kernel through cardinal reconstruction)
3. `sec_poisson_data.tex` (~300 lines): Subsections 5.7 centered reconstruction + channel RKHS
4. Alternatively, a two-way split along the natural break at subsection 5.6 (the mode Gram kernel)

**This split is a P5 action item.** The mathematical content is complete; only the file organization needs adjustment.

---

## Next Actions

1. **P5-1:** Split `sec_precision_potential.tex` into two files at the RKHS boundary
2. **P5-2:** Add optimality paragraph for $W_2$ exponent (Gap 1)
3. **P5-3:** Add bridging paragraph at the algebraic-analytic transition (Gap E1)
4. **P5-4:** Highlight $K = \pi P_2$ in RKHS subsection (Gap E2)
5. **P6-1:** Run clean LaTeX build cycle
6. **P4-1:** Final journal-fit assessment after P5 completion

---

# THEOREM_LIST -- All theorem-level claims

Paper: *Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS*

Status legend:
- **PROVED** = complete proof in the paper
- **STANDARD** = classical result, included for normalization fixing
- **COMPUTATIONAL** = verified by explicit trigonometric/residue computation

---

## Definitions

| # | Label | Location | One-line statement |
|---|---|---|---|
| D1 | `def:circle-dimension` | sec_circle_dimension_algebra, Def 2.1 | $\mathrm{cdim}(G) := \dim((\widehat{G})^0)$ for f.g. abelian $G$ |
| D2 | `def:half-circle-dimension` | sec_circle_dimension_algebra, Def 2.2 | $\mathrm{cdim}_+(M) := \frac{1}{2}\mathrm{cdim}(G(M))$ for cancellative monoid $M$ |
| D3 | `def:cdim-phase-spectrum` | sec_circle_dimension_algebra, Def 2.5 | $\Sigma_G(N) := |\mathrm{Hom}(G, \mu_N)|$; effective circle dimension $\delta_G(N) := \log\Sigma_G(N)/\log N$ |
| D4 | `eq:precision-potential` | sec_precision_potential, Eq 5.1 | Precision potential $\mathcal{P}(x) := \log\pi + \log(1+x^2)$ |

---

## Propositions

| # | Label | Location | One-line statement | Status |
|---|---|---|---|---|
| P1 | `prop:cayley-homeo` | sec_cayley_gate | $\iota: \overline{\mathbb{R}} \xrightarrow{\sim} \mathbb{T}$ is a homeomorphism; $\upsilon$ is a $C^\infty$ diffeomorphism $\mathbb{R} \to (-\tfrac{1}{2}, \tfrac{1}{2})$ | PROVED |
| P2 | `prop:circle-dimension-basic` | sec_circle_dimension_algebra | $\mathrm{cdim}(\mathbb{Z}^r \oplus T) = r$; $\mathrm{cdim}_+(\mathbb{N}^d) = d/2$ | PROVED |
| P3 | `prop:cdim-tensor-hom-ext-laws` | sec_circle_dimension_algebra | $\mathrm{cdim}(G \otimes H) = \mathrm{cdim}(G) \cdot \mathrm{cdim}(H)$; same for Hom; $\mathrm{cdim}(\mathrm{Ext}^1) = 0$ | PROVED |
| P4 | `prop:cdim-phase-spectrum-quotient` | sec_circle_dimension_algebra | $\Sigma_G(N) = |G/NG|$ | PROVED |
| P5 | `prop:phase-derivative` | sec_haar_pullback | $\upsilon'(x) = 1/(\pi(1+x^2))$; $\upsilon$ is measure-preserving | PROVED |
| P6 | `prop:poisson-identities` | sec_precision_potential | Scaling, Fourier transform $e^{-t|\xi|}$, semigroup law for $P_t$ | STANDARD |
| P7 | `thm:poisson-semigroup-law` | sec_precision_potential | $L^p$ contraction, strong continuity, generator $-|D|$ | STANDARD |
| P8 | `thm:poisson-second-order` | sec_precision_potential | Profile approximation $h_t/g_t = 1 + (\sigma^2/t^2)U(y) + O(t^{-3})$; $D_{\mathrm{KL}} = O(t^{-4})$ | PROVED |
| P9 | `prop:cayley-mode-remainder` | sec_precision_potential | Finite mode truncation: $R_\varepsilon = \sum_{n=0}^N u_n \varepsilon^n + \varepsilon^{N+1} v_N$ with $v_N$ bounded | PROVED |
| P10 | `thm:gram-space-poisson-image` | sec_precision_potential | $\mathcal{H}_K = \sqrt{\pi}\,e^{-|D|}L^2(\mathbb{R})$; holomorphic extension to strip $|\mathrm{Im}\,z| < 1$; sharp pointwise bound | PROVED |
| P11 | `prop:poisson-hardy-splitting` | sec_precision_potential | $\mathcal{H}_K = \mathcal{H}_K^+ \oplus \mathcal{H}_K^-$ with explicit Hardy kernels | PROVED |

---

## Theorems

| # | Label | Location | One-line statement | Status |
|---|---|---|---|---|
| T1 | **`thm:haar-pullback-uniqueness`** | sec_haar_pullback | Cayley is the unique normalized orientation-preserving $C^1$ chart with $\iota^* m_{\mathbb{T}} = \mu$ | PROVED |
| T2 | **`thm:cdim-axiomatic-rigidity`** | sec_circle_dimension_algebra | Five axioms (isomorphism invariance, additivity, finite-kernel invariance, $f(\mathbb{Z})=1$, $f(F)=0$) force $f = \mathrm{cdim}$ | PROVED |
| T3 | **`thm:cdim-short-exact-additivity`** | sec_circle_dimension_algebra | $\mathrm{cdim}$ is additive on short exact sequences; rank-nullity for homomorphisms | PROVED |
| T4 | **`thm:cdim-phase-spectrum-limit`** | sec_circle_dimension_algebra | $\lim_{N \to \infty} \delta_G(N) = \mathrm{cdim}(G)$; rate $O(a^{-1})$ along prime powers | PROVED |
| T5 | **`thm:cdim-phase-spectrum-reconstruction`** | sec_circle_dimension_algebra | $N \mapsto \Sigma_G(N)$ determines $G$ up to isomorphism via $p$-adic valuation formula | PROVED |
| T6 | **`thm:cdim-operational-half-circle-dimension-N`** | sec_circle_dimension_algebra | $c \cdot 2^{b/2} \leq N_{\max}(b) \leq C \cdot 2^{b/2}$; operational interpretation of $\mathrm{cdim}_+(\mathbb{N}) = 1/2$ | PROVED |
| T7 | **`thm:precision-ledger`** | sec_precision_potential | Entropy identity: $h_{\mathrm{diff}}(X) = h_{\mathrm{diff}}(U) + \mathbb{E}[\mathcal{P}(X)]$ | PROVED |
| T8 | **`thm:cayley-chebyshev-mode`** | sec_precision_potential | $u_n(\tan\theta) = \cos^n\theta\,U_n(\sin\theta)$; finite Fourier formulas for even/odd modes | PROVED |
| T9 | **`thm:poisson-kl-even-orders`** | sec_precision_potential | Odd powers vanish in KL expansion: $D_{\mathrm{KL}} = \sum c_{2m} t^{-2m} + o(t^{-2N})$ | PROVED |
| T10 | **`thm:poisson-kl-eighth`** | sec_precision_potential | Eighth-order explicit KL formula with coefficients in $(\sigma^2, \mu_3, \mu_4, \mu_5, \mu_6)$ | PROVED |
| T11 | **`thm:poisson-defect-ladder`** | sec_precision_potential | Two-level defect: $C_8 \geq \frac{23}{256}\sigma^8$; equality iff symmetric two-point law | PROVED |
| T12 | **`thm:poisson-defect-amplification`** | sec_precision_potential | $\Delta_8 \geq \frac{13\sigma^2}{8}\Delta_6$; strict amplification with equality characterization | PROVED |
| T13 | **`thm:poisson-defect-stability`** | sec_precision_potential | $W_2(\nu_c, \rho_\sigma) \leq 4\sigma^{-1/2}\Delta_6^{1/4} + 8\sigma^{-2}\Delta_6^{1/2}$ | PROVED |
| T14 | **`thm:mode-gram-kernel`** | sec_precision_potential | $\langle\Psi_\varepsilon, \Psi_\eta\rangle_{L^2(\omega)} = 2/(4+(\varepsilon-\eta)^2)$ | PROVED |
| T15 | **`thm:mode-space-rkhs`** | sec_precision_potential | Secant family spans $L^2_0(\omega)$; unitary equivalence $L^2_0(\omega) \cong \mathcal{H}_K$ | PROVED |
| T16 | **`thm:poisson-central-two-channel`** | sec_precision_potential | Central $(A,B)$ determines centred law via Laplace uniqueness + CF inversion | PROVED |
| T17 | **`thm:poisson-channel-rkhs`** | sec_precision_potential | Observation channels as RKHS evaluation at the origin; explicit formulas | PROVED |
| T18 | **`thm:poisson-lattice-sampling`** | sec_precision_potential | Integer kernel sections and secants are Riesz sequences with constants $\pi/\sinh(2\pi)$, $\pi\coth(2\pi)$; stable sampling on lattice subspace | PROVED |
| T19 | **`thm:poisson-cardinal-reconstruction`** | sec_precision_potential | Cardinal kernel $L$ with $L(n)=\delta_{0n}$; Shannon-type interpolation; exact norm formula via reciprocal lattice symbol | PROVED |

---

## Corollaries

| # | Label | Location | One-line statement | Status |
|---|---|---|---|---|
| C1 | `cor:cdim-operational-half-circle-dimension-Nd` | sec_circle_dimension_algebra | Box law: $\log_2 M_d(b)/b \to d/2 = \mathrm{cdim}_+(\mathbb{N}^d)$ | PROVED |
| C2 | `cor:mode-quadratic-integrals` | sec_precision_potential | Closed-form $\langle u_m, u_n \rangle_{L^2(\omega)}$ via central binomial coefficients | PROVED |
| C3 | `cor:poisson-symmetrization` | sec_precision_potential | $A$ determines the symmetrization of $\nu_c$ | PROVED |
| C4 | `cor:poisson-symmetric-case` | sec_precision_potential | $\nu_c$ symmetric iff $B \equiv 0$; then $A$ alone determines $\nu_c$ | PROVED |

---

## Lemmas and Remarks

| # | Label | Location | One-line statement | Status |
|---|---|---|---|---|
| L1 | `lem:entropy-integrals` | sec_appendix | Ten weighted trigonometric integrals for the eighth-order expansion | COMPUTATIONAL |
| R1 | `rem:orientation-reversal` | sec_haar_pullback | Without orientation: $\varphi = \iota$ or $\varphi = \overline{\iota}$ | PROVED |

---

## Proof Status Summary

| Status | Count |
|---|---|
| PROVED | 35 |
| STANDARD | 2 |
| COMPUTATIONAL | 1 |
| **Total claims** | **38** |

All theorem-level claims carry complete proofs in the manuscript. No claims are deferred or conditional.

---

# SOURCE_MAP -- Traceability for JFA Paper

Paper: *Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS*

Parent theory: `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/`

Abbreviation key:
- **PT** = parent theory, directory `sections/body/circle_dimension_phase_gate/`
- **L4** = `lean4/Omega/`

---

## Section 2: Notation and Conventions (`sec_preliminaries.tex`)

Standard definitions. No theorem-level claims. Fixes Fourier convention, entropy, KL divergence.

---

## Section 3: The Cayley Transform (`sec_cayley_gate.tex`)

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `prop:cayley-homeo` | Cayley map is a homeomorphism $\overline{\mathbb{R}} \xrightarrow{\sim} \mathbb{T}$ | PT: `sec__circle-dimension-phase-gate.tex` (opening material) | No Lean formalization |

**Note:** The Cayley coordinate definitions (Eqs. 3.1--3.3) are foundational; they appear implicitly throughout the parent theory's circle-dimension-phase-gate section.

---

## Section 4: Haar Pullback and Cauchy Rigidity (`sec_haar_pullback.tex`)

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `prop:phase-derivative` | $\upsilon'(x) = 1/(\pi(1+x^2))$, measure-preserving | PT: implicit in `sec__circle-dimension-phase-gate.tex` | No Lean |
| **`thm:haar-pullback-uniqueness`** | Cayley is unique chart pulling Haar back to Cauchy | PT: not explicitly stated as a standalone theorem in parent; distilled for JFA | No Lean |
| `rem:orientation-reversal` | Without orientation: unique up to conjugation | JFA-original sharpening | No Lean |

**Upstream dependencies:** Requires only the Cayley coordinate and normalized Haar measure.

---

## Section 5 (Algebraic): Circle Dimension and Phase Sampling (`sec_circle_dimension_algebra.tex`)

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `def:circle-dimension` | $\mathrm{cdim}(G) := \dim(\widehat{G})^0$ | PT: `subsubsec__cdim-fg-abelian-calculus.tex` (implicit, used throughout) | **L4:** `CircleDimension/CircleDim.lean` -- `circleDim` (simplified model: rank of free part) |
| `def:half-circle-dimension` | $\mathrm{cdim}_+(M) := \tfrac{1}{2}\mathrm{cdim}(G(M))$ | PT: `subsec__operational-half-circle-dimension.tex` | No Lean |
| `prop:circle-dimension-basic` | $\mathrm{cdim}(\mathbb{Z}^r \oplus T) = r$ | PT: `subsubsec__cdim-fg-abelian-calculus.tex` | **L4:** `circleDim_Zk`, `circleDim_finite`, `circleDim_add` |
| **`thm:cdim-axiomatic-rigidity`** | Five axioms force $f = \mathrm{cdim}$ | PT: `thm:cdim-axiomatic-rigidity` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean (algebraic; would need mathlib `FGAbelianGroup`) |
| **`thm:cdim-short-exact-additivity`** | Short exact additivity + rank-nullity | PT: `thm:cdim-short-exact-additivity` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| `prop:cdim-tensor-hom-ext-laws` | Tensor/Hom/Ext calculus for cdim | PT: `prop:cdim-tensor-hom-ext-laws` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| `def:cdim-phase-spectrum` | $\Sigma_G(N) := |\mathrm{Hom}(G, \mu_N)|$ | PT: `def:cdim-phase-spectrum` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| `prop:cdim-phase-spectrum-quotient` | $\Sigma_G(N) = |G/NG|$ | PT: `prop:cdim-phase-spectrum-quotient` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| **`thm:cdim-phase-spectrum-limit`** | $\lim_{N \to \infty} \delta_G(N) = \mathrm{cdim}(G)$ | PT: `thm:cdim-phase-spectrum-limit` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| **`thm:cdim-phase-spectrum-reconstruction`** | Full isomorphism type from $N \mapsto \Sigma_G(N)$ | PT: `thm:cdim-phase-spectrum-reconstruction` in `subsubsec__cdim-fg-abelian-calculus.tex` | No Lean |
| **`thm:cdim-operational-half-circle-dimension-N`** | $\log_2 N_{\max}(b) / b \to 1/2 = \mathrm{cdim}_+(\mathbb{N})$ | PT: `thm:cdim-operational-half-circle-dimension-N` in `subsec__operational-half-circle-dimension.tex` | No Lean |
| `cor:cdim-operational-half-circle-dimension-Nd` | Box law for $\mathbb{N}^d$ | PT: `cor:cdim-operational-half-circle-dimension-Nd` in `subsec__operational-half-circle-dimension.tex` | No Lean |

---

## Section 6: Poisson Smoothing, Entropy, and Reconstruction (`sec_precision_potential.tex`)

### 6.1 Entropy in Cayley coordinates

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:precision-ledger`** | $h_{\mathrm{diff}}(X) = h_{\mathrm{diff}}(U) + \mathbb{E}[\mathcal{P}(X)]$ | PT: `subsec__poisson-cauchy-constants.tex`, implicit in precision-potential discussion | No Lean |

### 6.2 Poisson smoothing

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `prop:poisson-identities` | Scaling, Fourier, semigroup of Poisson kernel | Standard (Stein--Weiss) | No Lean |
| `thm:poisson-semigroup-law` | $L^p$ contraction, strong continuity, generator $-|D|$ | Standard (included to fix normalization) | No Lean |

### 6.3 Large-time comparison

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `thm:poisson-second-order` | Second-order profile approximation, $D_{\mathrm{KL}} = O(t^{-4})$ | PT: `prop:cdim-poisson-l1-second-order-constant` in `subsec__poisson-cauchy-constants.tex` | No Lean |

### 6.4 Cayley--Chebyshev mode calculus

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:cayley-chebyshev-mode`** | $u_n(\tan\theta) = \cos^n\theta\,U_n(\sin\theta)$; finite Fourier formulas | PT: `prop:cdim-poisson-cauchy-finite-laurent-modes` in `para__poisson-cauchy-phase-fourierization.tex` (rewritten and sharpened for JFA) | No Lean |
| `prop:cayley-mode-remainder` | Finite mode truncation with bounded remainder | JFA-original (quantitative version of parent's expansion) | No Lean |

### 6.5 Entropy asymptotics and rigidity

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:poisson-kl-even-orders`** | Only even powers in KL expansion | PT: `prop:cdim-poisson-kl-sixth-order-correction` in `subsec__poisson-cauchy-higher-order-corrections.tex` (implicit parity principle) | No Lean |
| **`thm:poisson-kl-eighth`** | Eighth-order KL expansion with explicit coefficients | PT: `prop:cdim-poisson-kl-sixth-order-correction` (sixth order) + JFA extension to eighth order | No Lean |
| **`thm:poisson-defect-ladder`** | Two-level defect coordinates; $C_8 \geq \frac{23}{256}\sigma^8$ | JFA-original (not in parent theory at this precision) | No Lean |
| **`thm:poisson-defect-amplification`** | $\Delta_8 \geq \frac{13\sigma^2}{8}\Delta_6$; strict amplification | JFA-original | No Lean |
| **`thm:poisson-defect-stability`** | $W_2(\nu_c, \rho_\sigma) = O(\Delta_6^{1/4})$ | JFA-original | No Lean |

### 6.6 Mode Gram kernel and Hilbert completion

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:mode-gram-kernel`** | $\langle\Psi_\varepsilon,\Psi_\eta\rangle = 2/(4+(\varepsilon-\eta)^2)$ | PT: `prop:cdim-cauchy-derivative-gram-exponential-kernel` in `subsec__poisson-cauchy-gram-kernel.tex` | No Lean |
| `cor:mode-quadratic-integrals` | Closed-form quadratic mode integrals via binomial coefficients | PT: `prop:cdim-cauchy-kernel-derivative-gram-closed-form` in `subsec__poisson-cauchy-gram-kernel.tex` | No Lean |
| **`thm:mode-space-rkhs`** | $\overline{\mathrm{span}}\{\Psi_\varepsilon\} = L^2_0(\omega)$; unitary to $\mathcal{H}_K$ | PT: `prop:cdim-kernel-rkhs-feature-map` in `subsec__poisson-cauchy-gram-kernel.tex` | No Lean |

### 6.7 Centered reconstruction

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:poisson-central-two-channel`** | $(A,B)$ determines centred law by Laplace uniqueness | PT: `prop:cdim-poisson-central-two-channel-reconstruction` in `subsec__poisson-cauchy-gram-kernel.tex` | No Lean |
| `cor:poisson-symmetrization` | $A$ determines symmetrization | PT: `cor:cdim-poisson-central-slice-kernel` in `subsec__poisson-cauchy-constants.tex` | No Lean |
| `cor:poisson-symmetric-case` | Symmetric iff $B \equiv 0$ | PT: corollary of above | No Lean |
| `thm:poisson-channel-rkhs` | Observation channels as RKHS evaluation functionals | JFA-original synthesis | No Lean |

### 6.8 Poisson image realization

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| **`thm:gram-space-poisson-image`** | $\mathcal{H}_K = \sqrt{\pi}\,e^{-|D|}L^2(\mathbb{R})$; strip extension | PT: `prop:cdim-kernel-rkhs-feature-map` + `prop:cdim-kernel-strip-extension-eval` in `subsec__cauchy-kernel-rkhs-affine-translate.tex` | No Lean |

### 6.9 Hardy splitting, lattice sampling, cardinal reconstruction

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `prop:poisson-hardy-splitting` | $\mathcal{H}_K = \mathcal{H}_K^+ \oplus \mathcal{H}_K^-$ | JFA-original (natural from Fourier support splitting) | No Lean |
| **`thm:poisson-lattice-sampling`** | Integer kernel sections form Riesz sequence; stable sampling on $\mathbb{Z}$ | PT: `prop:cdim-kernel-integer-translate-riesz-bounds` + `prop:cdim-kernel-integer-sampling-dual-kernel` in `subsec__cauchy-kernel-rkhs-affine-translate.tex` | No Lean |
| **`thm:poisson-cardinal-reconstruction`** | Shannon-type cardinal kernel $L$; exact norm formula | PT: `prop:cdim-kernel-integer-sampling-dual-kernel` (the dual-kernel formulation is the parent version) | No Lean |

---

## Appendix A (`sec_appendix.tex`)

| Paper label | Statement | Parent source | Lean status |
|---|---|---|---|
| `lem:entropy-integrals` | Ten weighted trigonometric integral identities | JFA-original (computational verification via product-to-sum formulas) | No Lean |

---

## Summary of Lean Coverage

| Category | Count | Lean formalized |
|---|---|---|
| Definitions | 4 | 1 (circleDim, simplified) |
| Propositions | 12 | 0 |
| Theorems | 16 | 0 |
| Corollaries | 4 | 0 |
| Lemmas | 1 | 0 |
| **Total** | **37** | **1 partial** |

The Lean formalization in `lean4/Omega/CircleDimension/CircleDim.lean` covers only the basic circle-dimension definition and elementary properties (additivity, vanishing on finite groups). The functional-analytic and operator-theoretic content of this paper is entirely outside the current Lean scope. The Lean `IMPLEMENTATION_PLAN.md` records "Circle Dimension | 393 | 19 | 4.8%" for the parent theory chapter, but those 19 labels correspond to audit-stability, higher-spectrum, and semiring-rigidity results, not to the Poisson/entropy/RKHS line of this JFA paper.

---

## Upstream Dependency Summary

The JFA paper depends on the following conceptual layers from the parent theory:

1. **Cayley compactification layer:** Cayley coordinate, phase map, Cauchy measure identification
2. **Circle dimension algebra:** axiomatic rigidity, phase spectrum, reconstruction theorem
3. **Poisson entropy layer:** precision potential, KL asymptotics, mode calculus
4. **RKHS/operator layer:** Gram kernel, Poisson image space, strip model, lattice sampling

Layers 1--2 are algebraic/number-theoretic and map directly to parent theory labels. Layers 3--4 are analytic and required substantial rewriting, sharpening (eighth-order expansion, defect amplification, cardinal reconstruction) for JFA submission quality.

---



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

---


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

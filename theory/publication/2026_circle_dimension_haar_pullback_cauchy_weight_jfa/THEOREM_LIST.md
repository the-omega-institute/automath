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

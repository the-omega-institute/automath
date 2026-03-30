# SOURCE_MAP: Dynamical zeta Finite Part and Spectral Fingerprint (ETDS)

Paper direction code: H

## Upstream dependency

- **Paper F** (POM core, strong dependency): the primitive matrix formalism, Perron--Frobenius framework, and reduced determinant conventions are inherited from the parent theory.

## Source directories in parent theory

| Directory | Files | Lines | Role in this paper |
|---|---|---|---|
| `zeta_finite_part/syntax/` | 4 | 836 | DFA density dichotomy, Zeckendorf non-regularity (excluded from main paper, kept in `sec_syntax_zeta.tex`) |
| `zeta_finite_part/online_kernel/` | 11 | 2,822 | Synchronisation kernel, completed determinant, genus-6 curve (excluded from main paper, kept in `sec_online_kernel.tex`) |
| `zeta_finite_part/operator/` | 8 | 1,446 | Fredholm--Witt bridge, cyclic-block realisation, spectral-gap CLT (excluded from main paper, kept in `sec_operator.tex`) |
| `zeta_finite_part/finite_part/` | 27 | 5,149 | Core: finite-part formula, cyclic reconstruction, finite-group extensions, shadows, appendices |

## Theorem-to-source map

### sec_introduction.tex

| Label | Statement | Source |
|---|---|---|
| `thm:intro-finite-part` | Finite-part formula at the Perron pole | Summary of `thm:finite-part-primitive-closed-form` + `cor:finite-part-mertens-asymptotic` |
| `thm:intro-cyclic-reconstruction` | Cyclic reconstruction of the reduced spectrum (3 parts) | Summary of `thm:finite-part-cyclic-lift-spectrum-identifiability` + `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction` + `cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum` |
| `thm:intro-finite-group` | Primitive determinant calculus for finite-group extensions (3 parts + S3) | Summary of Sec 4--5 theorems |

### sec_preliminaries.tex

| Label | Statement | Source |
|---|---|---|
| `prop:prelim-trace-primitive` | Euler product for dynamical zeta | Classical: Bowen--Lanford 1970, Manning 1971 |
| `lem:primitive-orbit-asymptotic` | Primitive orbit count asymptotic p_n(A) = lambda^n/n + O(...) | Perron--Frobenius + Mobius inversion |
| `def:kernel-rh` | Square-root bound Lambda(A) <= lambda^{1/2} | New definition |
| `def:abel-finite-part` | Abel finite-part constant FP(A) | New definition |

### sec_finite_part.tex (Section 3)

| Label | Statement | Source |
|---|---|---|
| `thm:finite-part-primitive-closed-form` | Closed-form formula for FP(A) | `finite_part/` -- core new result |
| `prop:finite-part-residue-reduced-determinant` | C(A) = prod(1 - mu_j/lambda)^{-1} | Standard spectral factorisation |
| `cor:finite-part-mertens-asymptotic` | Orbit-Mertens asymptotic | Consequence of `thm:finite-part-primitive-closed-form` |
| `thm:finite-part-cyclic-lift-reduced-constant-closed` | C(A^{<q>}) closed form via root-of-unity products | `finite_part/` -- new |
| `prop:finite-part-cyclic-lift-dirichlet-multiple-sum` | Psi_q(A) = sum u_{qm}/m expansion | `finite_part/` -- new |
| `prop:finite-part-cyclic-lift-mobius-inversion` | Mobius inversion recovering u_n from Psi | `finite_part/` -- new |
| `thm:finite-part-cyclic-lift-spectrum-identifiability` | Full cyclic data determine F_A | `finite_part/` -- new |
| `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction` | One root-of-unity layer (q >= d) suffices | `finite_part/` -- new |
| `cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum` | Zeta values at torsion points determine spectrum | Consequence |
| `rem:finite-part-fibonacci-example` | Fibonacci toy example | New |
| `cor:finite-part-single-layer-square-root-test` | Square-root test from one layer | Consequence |
| `cor:finite-part-gap-positive` | Gap(A) > 0 | Consequence of `thm:finite-part-primitive-closed-form` |

### sec_chebotarev.tex (Section 4)

| Label | Statement | Source |
|---|---|---|
| `prop:class-indicator-expansion` | Conjugacy-class indicator expansion in irreducible characters | Standard representation theory |
| `prop:kernel-peter-weyl-block-diagonalisation` | Peter--Weyl determinant factorisation of tilde{A} | Standard: Boyle--Schmieding 2017 framework |
| `thm:class-function-linearisation` | Class-function logarithm = sum of twisted log-determinants | New synthesis |
| `cor:class-function-adams-mobius` | Adams--Mobius primitive inversion formula | **Key new result** |
| `lem:adams-coefficients-bounded` | Adams coefficients bounded by (dim rho)^2 | New |
| `cor:primitive-peter-weyl-determinant` | Irreducible-channel determinant formula for Pi_rho | **Key new result** |
| `cor:primitive-peter-weyl-trace` | Primitive Peter--Weyl trace formula | Consequence |
| `thm:class-primitive-decomposition` | Conjugacy-class primitive decomposition | New |
| `cor:class-artin-mobius-trace` | Conjugacy-class Artin--Mobius trace formula | Consequence |
| `thm:class-mertens-explicit` | Explicit class Mertens theorem under twisted spectral gap | **Key new result** |
| `thm:class-mertens-fourier` | Non-abelian Fourier reconstruction of class Mertens constants | **Key new result** |

### sec_shadows.tex (Section 5)

| Label | Statement | Source |
|---|---|---|
| `def:normalised-primitive-class-profile` | Normalised primitive class profile B_A(C) | New definition |
| `thm:quotient-functoriality` | Quotient functoriality for primitive class profiles | New |
| `cor:abelian-cyclic-shadow` | Abelian and cyclic shadows | Consequence |
| `thm:abelian-shadow-defect` | Abelian shadow and genuine non-abelian defect (orthogonal splitting) | **Key new result** |
| `thm:cyclic-detection-boundary` | Exact boundary of cyclic detection | **Key new result** |
| `thm:quadratic-adams-obstruction` | Quadratic Adams obstruction | New |
| `prop:s3-example-channels` | S3-example: twisted channels | New computation |
| `prop:s3-example-primitive-channels` | S3-example: primitive channels and Pi values | New computation |
| `cor:s3-example-profile` | S3-example: primitive profile, class constants, energy ratio | New computation |

### sec_appendices.tex (Appendices A--C)

| Label | Statement | Source |
|---|---|---|
| `thm:finite-part-reduced-determinant-group-inverse-gradient` | Reduced-determinant gradient formula (group inverse) | `finite_part/` -- new |
| `thm:logM-holomorphic-variation` | Holomorphic variation of FP(A_theta) | `finite_part/` -- new |
| `thm:logM-truncation-bound` | Explicit truncation bound for FP_K(A) | `finite_part/` -- new |
| `thm:finite-part-nyquist-parseval-aliasing` | Parseval and aliasing formula for root-of-unity sampling | `finite_part/` -- new |
| `cor:finite-part-nyquist-error-exp` | Exponential bound for sampling error | Consequence |
| `prop:finite-part-dirichlet-torsion-gauss-expansion` | Gauss expansion for character sums at roots of unity | `finite_part/` -- new |
| `thm:finite-part-dirichlet-character-inversion-prime` | Character inversion for prime moduli | `finite_part/` -- new |
| `cor:finite-part-near-rh-q-axis-envelope` | Growth criterion for square-root bound | Consequence |
| `thm:finite-part-boundary-multiplicity-qaxis-energy` | Boundary multiplicities from Cesaro averages | `finite_part/` -- new |
| `prop:finite-part-torsion-table-galois-covariance` | Galois covariance of root-of-unity values | New |
| `cor:finite-part-torsion-table-galois-certificate` | Rationality criterion from Galois covariance | Consequence |
| `thm:finite-part-single-layer-torsion-near-rh` | Finite criterion for square-root bound from one layer | New synthesis |
| `thm:finite-part-cyclic-lift-polylog-dirichlet-xi` | Dirichlet series for cyclic-lift discrepancy | `finite_part/` -- new |
| `prop:finite-part-residue-constant-rh-squeeze` | Residue constant bounds under square-root bound | `finite_part/` -- new |
| `thm:finite-part-residue-drift-trichotomy` | Linear growth of reduced determinant for growing families | `finite_part/` -- new |

## Lean 4 formalisation status

| Lean file | Labels covered | Relevant paper theorems |
|---|---|---|
| `Omega/Zeta/DynZeta.lean` (131 lines) | `fredholmGoldenMean_det`, `goldenMean_trace_values`, `goldenMean_trace_recurrence`, `goldenMean_primitive_orbit_numerators`, `degeneracy_ghost_coefficients`, `goldenMean_cayleyHamilton` | Concrete golden-mean SFT: det(I-zA) = 1-z-z^2, trace sequence (Lucas), Mobius inversion for p_n, Cayley--Hamilton |
| `Omega/Zeta/CyclicDet.lean` (155 lines) | `cyclicPerm2..6_fredholm_det`, `euler_factor_n2..n4`, `cyclicPerm_periodicity` | Cyclic permutation determinant 1-t^n, Euler factor det(I-r*alpha*Pi_n), periodicity |

**Coverage note**: The Lean formalisation currently covers 0.4% of the parent chapter's 4,524 labelled environments (17 labels). The formalised results are concentrated on the golden-mean concrete model and cyclic permutation determinants. None of the paper's main abstract theorems (finite-part formula, cyclic reconstruction, Adams--Mobius inversion, class Mertens theorem) are yet formalised.

## Excluded sections (present in directory but not in main.tex)

| File | Content | Reason for exclusion |
|---|---|---|
| `sec_syntax_zeta.tex` | DFA density dichotomy, binary primes, Zeckendorf non-regularity, natural boundary | Not part of the ETDS narrative; tangential to core dynamical-systems audience |
| `sec_operator.tex` | Fredholm--Witt bridge, cyclic-block realisation, spectral-gap CLT | Framework results that support the main story but were removed to sharpen focus |
| `sec_online_kernel.tex` | 10-state synchronisation kernel, completed determinant, genus-6 curve, twisted Perron roots | Concrete worked example; too specialised for ETDS scope |

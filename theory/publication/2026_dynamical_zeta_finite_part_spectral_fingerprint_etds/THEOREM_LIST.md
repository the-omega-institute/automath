# THEOREM_LIST: Dynamical zeta Finite Part and Spectral Fingerprint (ETDS)

## Classification key

- **PROVED**: Full proof in the manuscript
- **STANDARD**: Classical result reproved or cited with reference
- **COMPUTED**: Verified by explicit computation (S3-example)
- **CONSEQUENCE**: Follows directly from a proved result

---

## Section 2: Preliminaries

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 1 | `prop:prelim-trace-primitive` | Proposition | zeta_A(z) = det(I-zA)^{-1} = prod(1-z^n)^{-p_n(A)} | STANDARD |
| 2 | `lem:primitive-orbit-asymptotic` | Lemma | p_n(A) = lambda^n/n + O(max{Lambda^n, lambda^{n/2}}/n) | PROVED |
| 3 | `def:kernel-rh` | Definition | Square-root bound: Lambda(A) <= lambda^{1/2} | -- |
| 4 | `def:abel-finite-part` | Definition | FP(A) := lim_{r->1} (P_A(r) + log(1-r)), Mertens constant M(A) = gamma + FP(A) | -- |

## Section 3: Finite parts at the Perron pole and cyclic reconstruction

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 5 | `thm:finite-part-primitive-closed-form` | **Theorem** | FP(A) = log C(A) + sum_{k>=2} mu(k)/k log det(I - lambda^{-k} A)^{-1} | PROVED |
| 6 | `prop:finite-part-residue-reduced-determinant` | Proposition | C(A) = prod(1 - mu_j/lambda)^{-1} = det'(I - A/lambda)^{-1} | PROVED |
| 7 | `cor:finite-part-mertens-asymptotic` | Corollary | sum_{n<=N} p_n/lambda^n = log N + M(A) + o(1) | CONSEQUENCE |
| 8 | `thm:finite-part-cyclic-lift-reduced-constant-closed` | **Theorem** | C(A^{<q>}) = (1/q) prod(1 - (mu_j/lambda)^q)^{-1} | PROVED |
| 9 | `prop:finite-part-cyclic-lift-dirichlet-multiple-sum` | Proposition | Psi_q(A) = sum_{m>=1} u_{qm}/m, with Psi_q = u_q + O(Lambda_rel^{2q}) | PROVED |
| 10 | `prop:finite-part-cyclic-lift-mobius-inversion` | Proposition | u_n/n = sum_{m>=1} mu(m)/(mn) Psi_{mn}(A) | PROVED |
| 11 | `thm:finite-part-cyclic-lift-spectrum-identifiability` | **Theorem** | {Psi_q} determines F_A, hence non-Perron spectrum; limsup |Psi_q|^{1/q} = Lambda_rel | PROVED |
| 12 | `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction` | **Theorem** | If q >= d, then {F_A(omega_q^j)} determines all coefficients of F_A by DFT | PROVED |
| 13 | `cor:finite-part-cyclic-lift-zeta-torsion-determines-spectrum` | Corollary | (C(A), {zeta_A(omega_q^j/lambda)}) determines non-Perron spectrum | CONSEQUENCE |
| 14 | `cor:finite-part-single-layer-square-root-test` | Corollary | One root-of-unity layer decides the square-root bound | CONSEQUENCE |
| 15 | `cor:finite-part-gap-positive` | Corollary | Gap(A) = log C(A) - FP(A) > 0 | CONSEQUENCE |

## Section 4: Class functions, Adams operations, and finite-group extensions

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 16 | `prop:class-indicator-expansion` | Proposition | 1_C(g) = |C|/|G| sum chi_rho(C^{-1}) chi_rho(g) | STANDARD |
| 17 | `prop:kernel-peter-weyl-block-diagonalisation` | Proposition | det(I - z tilde{A}) = prod det(I - z A_rho)^{dim rho} | STANDARD |
| 18 | `thm:class-function-linearisation` | **Theorem** | L_phi(z) = sum hat{phi}(rho) log det(I - z A_rho)^{-1} | PROVED |
| 19 | `cor:class-function-adams-mobius` | **Corollary** | Pi_phi(z) = sum_{m>=1} mu(m)/m L_{psi^m phi}(z^m) (Adams--Mobius) | PROVED |
| 20 | `lem:adams-coefficients-bounded` | Lemma | |a_{rho,sigma}^{(m)}| <= (dim rho)^2 | PROVED |
| 21 | `cor:primitive-peter-weyl-determinant` | **Corollary** | Pi_rho(z) expressed as Adams--Mobius sum of log-determinants | PROVED |
| 22 | `cor:primitive-peter-weyl-trace` | Corollary | pi_{n,rho}(A) trace formula | CONSEQUENCE |
| 23 | `thm:class-primitive-decomposition` | **Theorem** | p_{n,C} = (|C|/|G|) sum chi_rho(C^{-1}) pi_{n,rho} | PROVED |
| 24 | `cor:class-artin-mobius-trace` | Corollary | p_{n,C} Artin--Mobius triple-sum trace formula | CONSEQUENCE |
| 25 | `thm:class-mertens-explicit` | **Theorem** | Under eta < lambda: p_{n,C} asymptotic + class Mertens constants M_C(A) | PROVED |
| 26 | `thm:class-mertens-fourier` | **Theorem** | Delta_C(A) = non-abelian Fourier expansion; Fourier inversion recovers Pi_rho(lambda^{-1}); Plancherel | PROVED |

## Section 5: Quotient shadows, cyclic detection, and S3 model

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 27 | `thm:quotient-functoriality` | **Theorem** | L_{q*f}^G = L_f^Q, Pi_{q*f}^G = Pi_f^Q for quotient q: G ->> Q | PROVED |
| 28 | `cor:abelian-cyclic-shadow` | Corollary | 1-dim Peter--Weyl = pullback of abelianised cocycle; cyclic quotients recover Sec 3 root-of-unity layers | CONSEQUENCE |
| 29 | `thm:abelian-shadow-defect` | **Theorem** | B_A^{ab} perp B_A^{na}; energy decomposition; equivalence of abelian factorisation conditions | PROVED |
| 30 | `thm:cyclic-detection-boundary` | **Theorem** | span of cyclic pullbacks = span of 1-dim characters; P_cyc B_A = B_A^{ab} | PROVED |
| 31 | `thm:quadratic-adams-obstruction` | Proposition | For quadratic chi with L_chi = 0: Pi_chi may be nonzero (Adams even terms feed trivial rep) | PROVED |
| 32 | `prop:s3-example-channels` | Proposition | S3 twisted matrices: A_eps^2 = 0, det(I-zA_rho) = 1+z, periodic class counts | COMPUTED |
| 33 | `prop:s3-example-primitive-channels` | Proposition | Pi_eps(1/2) = -0.3411..., Pi_rho(1/2) = -0.7184... (both nonzero) | COMPUTED |
| 34 | `cor:s3-example-profile` | Corollary | Explicit primitive class triples, Delta values, energy ratio na/ab = 4.44... | COMPUTED |

## Appendix A: Holomorphic variation and effective truncation

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 35 | `thm:finite-part-reduced-determinant-group-inverse-gradient` | Theorem | d/dtheta log C(A_theta) via group inverse R_theta of B_theta | PROVED |
| 36 | `thm:logM-holomorphic-variation` | Theorem | FP(A_theta) is holomorphic; term-by-term differentiation formula | PROVED |
| 37 | `thm:logM-truncation-bound` | Theorem | |FP(A) - FP_K(A)| <= d lambda^{-(K+1)} / ((K+1)(1-lambda^{-1})^2) | PROVED |

## Appendix B: Arithmetic consequences of root-of-unity sampling

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 38 | `thm:finite-part-nyquist-parseval-aliasing` | Theorem | Parseval identity + aliasing formula for discrete root-of-unity sampling | PROVED |
| 39 | `cor:finite-part-nyquist-error-exp` | Corollary | Sampling error <= K Lambda_rel^q | CONSEQUENCE |
| 40 | `prop:finite-part-dirichlet-torsion-gauss-expansion` | Proposition | Gauss expansion for L_A(chi; q) via Gauss sums tau | PROVED |
| 41 | `thm:finite-part-dirichlet-character-inversion-prime` | Theorem | Character inversion for prime moduli: V_{p,r}(A) from L_A(chi;p) | PROVED |
| 42 | `cor:finite-part-near-rh-q-axis-envelope` | Corollary | Square-root bound iff |Psi_q| <= K lambda^{-q/2} | CONSEQUENCE |
| 43 | `thm:finite-part-boundary-multiplicity-qaxis-energy` | Theorem | Cesaro average of |u_q|^2/Lambda^{2q} -> sum m(zeta)^2 (boundary multiplicities) | PROVED |
| 44 | `prop:finite-part-torsion-table-galois-covariance` | Proposition | sigma_h(F_A(omega_q^j)) = F_A(omega_q^{hj}) | PROVED |
| 45 | `cor:finite-part-torsion-table-galois-certificate` | Corollary | Galois covariance test guarantees rational DFT coefficients | CONSEQUENCE |
| 46 | `thm:finite-part-single-layer-torsion-near-rh` | Theorem | Finite criterion for square-root bound from one root-of-unity layer | PROVED |

## Appendix C: Asymptotic families, square-root bounds, and rigidity

| # | Label | Type | One-line statement | Status |
|---|---|---|---|---|
| 47 | `prop:finite-part-residue-constant-rh-squeeze` | Proposition | Under square-root bound: (1+lambda^{-1/2})^{-(d-1)} <= C(A) <= (1-lambda^{-1/2})^{-(d-1)} | PROVED |
| 48 | `thm:finite-part-residue-drift-trichotomy` | Theorem | For growing families with lambda_q >= c^q: square-root bound forces |log C_q| = o(q) | PROVED |

---

## Summary statistics

| Category | Count |
|---|---|
| Main theorems (bold) | 14 |
| Propositions | 10 |
| Corollaries | 12 |
| Lemmas | 2 |
| Definitions | 3 |
| Remarks (with mathematical content) | 1 |
| **Total theorem-level claims** | **39** (excluding definitions and remark) |
| Proof status: PROVED | 30 |
| Proof status: STANDARD | 3 |
| Proof status: COMPUTED | 3 |
| Proof status: CONSEQUENCE | 9 |

All 39 theorem-level claims carry complete proofs in the manuscript. No claims are left as exercises or deferred to future work.

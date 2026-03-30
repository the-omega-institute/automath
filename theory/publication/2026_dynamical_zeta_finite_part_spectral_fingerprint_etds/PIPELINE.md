# TRACK_BOARD: Dynamical zeta Finite Part and Spectral Fingerprint (ETDS)

**Paper**: H -- Dynamical zeta-Function Finite Part and Spectral Fingerprint
**Target**: Ergodic Theory and Dynamical Systems (ETDS)
**Last updated**: 2026-03-30

---

## Pipeline stages

| Stage | Name | Status | Date | Notes |
|---|---|---|---|---|
| P0 | Scope & journal fit | DONE | pre-2026-03-30 | README.md written; ETDS primary, JEMS stretch, Nonlinearity fallback |
| P1 | Traceability | DONE | 2026-03-30 | SOURCE_MAP.md and THEOREM_LIST.md created. 48 labelled claims, 39 theorem-level, all proved. Lean coverage: 0.4% (17/4524 labels in parent chapter) |
| P2 | Research extension | DONE | 2026-03-30 | P2_EXTENSION_NOTE_2026-03-30.md created. Three theorem packages identified. Five gaps flagged. Scope cuts confirmed (syntax, operator, online_kernel sections excluded) |
| P3 | Journal-fit rewrite | DONE | 2026-03-30 | P3_REWRITE_NOTE_2026-03-30.md created. Abstract rewritten (~150 words). Introduction rewritten (Theorem A/B/C style, ETDS tradition connections). Conclusion expanded (3 open problems, transfer-operator connections). Bibliography cleaned (15 uncited entries removed, 15 cited entries retained). Style pass done. All files under 800 lines |
| P4 | Writing polish | DONE | 2026-03-30 | ETDS-style P4 pass completed. Added literature-facing clarification to Remark 4.14, made the `S3` example verify `eta < lambda` explicitly, and checked the current build artifact (`main.pdf`) at 36 pages. No P4 blockers; ready for P5 |
| P5 | Internal review | NOT STARTED | -- | Pre-submission quality gate per Omega charter: verify new axioms/assumptions explicit, conclusions traceable, results reproducible, scope/failure modes recorded |
| P6 | Lean audit gate | NOT STARTED | -- | Current Lean coverage 0.4%. Priority targets: `fredholmGoldenMean_det` (done), cyclic permutation det (done), trace recurrence (done). Next: abstract `thm:finite-part-primitive-closed-form` requires real-analysis Lean infrastructure not yet available |
| P7 | Submission | NOT STARTED | -- | Target: ETDS via Editorial Manager. AMS subject classification 37B10, 37D35, 11M41, 20C15 already in main.tex. Submission metadata is still placeholder |

---

## Gap tracker

| ID | Description | Severity | Owner | Status |
|---|---|---|---|---|
| G1 | Twisted spectral-gap hypothesis: no dynamical criteria given for eta < lambda | Low | -- | Closed in P4. Remark 4.14 expanded and the `S3` example now records `eta=1<2=lambda` explicitly |
| G2 | Adams decomposition: no general formula for a_{rho,sigma}^{(m)} | Low | -- | Acceptable for ETDS; coefficients are standard rep-theory |
| G3 | FP(A) as spectral invariant: independence discussion missing | Low | -- | Add 1--2 sentences to discussion |
| G4 | S3 numerical values: no formal error bound or verification script | Medium | -- | Open. Not a P4 blocker, but still a P5/P7 reproducibility risk |
| G5 | Appendix B bulk: Dirichlet/Gauss material may be too number-theoretic for ETDS | Low | -- | Accepted in P4. Current build is 36pp, so no pre-emptive cut is needed |
| G6 | Submission metadata still placeholder in `main.tex` (`[Author]`, `[Affiliation]`, `[email]`) | Low | -- | Open. Not a P4 blocker, but a real P7 submission blocker |

---

## Section-level status

| Section | File | Lines | Status |
|---|---|---|---|
| Title / Abstract | main.tex | 100 | P3: Abstract rewritten (~150 words, ETDS style) |
| 1. Introduction | sec_introduction.tex | 276 | P3: Rewritten. Theorems A/B/C. ETDS tradition. Comparison table. Section roadmap |
| 2. Preliminaries | sec_preliminaries.tex | 194 | Written. Notation fixed |
| 3. Finite parts + cyclic reconstruction | sec_finite_part.tex | 418 | Written, all proofs complete |
| 4. Class functions + finite-group extensions | sec_chebotarev.tex | 619 | Written, all proofs complete. P4: twisted spectral-gap remark expanded for ETDS framing |
| 5. Shadows + S3 model | sec_shadows.tex | 653 | Written, all proofs complete. P4: S3 example now verifies `eta < lambda` explicitly |
| 6. Discussion + open problems | sec_conclusion.tex | 72 | P3: Expanded. Three open problems (spectral gap, non-abelian arithmetic, transfer operators) |
| App A. Holomorphic variation | sec_appendices.tex (A) | ~100 | Written. Opener cleaned (P3) |
| App B. Arithmetic consequences | sec_appendices.tex (B) | ~240 | Written. Opener cleaned (P3). Consider condensing (P4) |
| App C. Growing families | sec_appendices.tex (C) | ~90 | Written. Opener cleaned (P3) |
| References | references.bib | 151 | P3: 15 entries, all cited. Uncited entries removed |

**Excluded files** (in directory, not in main.tex):
- sec_syntax_zeta.tex (314 lines) -- DFA/Zeckendorf material
- sec_operator.tex (197 lines) -- Fredholm--Witt / CLT
- sec_online_kernel.tex (358 lines) -- synchronisation kernel

---

## Dependencies

| Direction | Paper | Relationship |
|---|---|---|
| Upstream | F (POM core) | Strong: primitive matrix formalism, Perron--Frobenius, reduced determinant |
| Downstream | J (zeta-completion) | Strong: H is a necessary precursor for J |

---

## Quality gate checklist (pre-submission)

- [ ] New axioms/assumptions explicit? (twisted spectral gap eta < lambda: YES, explicitly stated)
- [ ] Key conclusions traceable to base layer? (YES: all via Perron--Frobenius + Mobius inversion + character theory)
- [ ] Results reproducible? (PARTIAL: proofs are self-contained; numerical S3 values need script)
- [ ] Scope and failure modes recorded? (YES: conclusion states three open problems; twisted spectral-gap role delineated in Remark 4.14)

---

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

---

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

---



# P2 Extension Note: Dynamical zeta Finite Part and Spectral Fingerprint

**Date**: 2026-03-30
**Target journal**: Ergodic Theory and Dynamical Systems (ETDS)
**Paper direction**: H

---

## 1. Main theorem package for ETDS submission

The paper offers ETDS three independent but interlocking theorem packages.

### Package A: Finite-part primitive calculus (Section 3)

**Flagship**: `thm:finite-part-primitive-closed-form` -- The finite-part constant FP(A) at the Perron pole of zeta_A admits a closed primitive-orbit formula

$$
\mathrm{FP}(A) = \log C(A) + \sum_{k \ge 2} \frac{\mu(k)}{k} \log\det(I - \lambda^{-k} A)^{-1}.
$$

This is the natural SFT analogue of the constant in Mertens' theorem for primes. The formula is new: while the Euler product and Mobius inversion for SFT zeta functions are classical (Bowen--Lanford, Manning, Parry--Pollicott), nobody has isolated and named the finite-part constant at the Perron pole or given its primitive-orbit closed form.

**ETDS fit**: Direct analogy with the prime number theorem / Mertens' theorem in the symbolic-dynamics setting. This is squarely within the journal's scope.

### Package B: Cyclic reconstruction (Section 3, second half)

**Flagship**: `thm:finite-part-cyclic-lift-spectrum-identifiability` + `thm:finite-part-cyclic-lift-single-q-torsion-reconstruction` -- The cyclic-lift constants {C(A^{<q>})} determine the reduced spectral polynomial F_A, and a single root-of-unity layer of order q >= d already suffices.

This is a spectral rigidity result: the non-Perron eigenvalues of A (with multiplicity) are recoverable from a finite set of torsion data. The mechanism is clean -- Mobius inversion on multiples to recover power sums, then Newton's identities. The single-layer result uses discrete Fourier inversion at roots of unity and is sharp in the threshold q >= d.

**ETDS fit**: Spectral rigidity and inverse spectral problems for SFTs are a classical ETDS topic (Lind--Marcus, Boyle--Handelman).

### Package C: Non-abelian primitive determinant calculus (Sections 4--5)

**Flagship cluster**:
- `cor:class-function-adams-mobius` -- Adams--Mobius primitive inversion: Pi_phi(z) = sum mu(m)/m L_{psi^m phi}(z^m)
- `cor:primitive-peter-weyl-determinant` -- Irreducible-channel determinant formula for Pi_rho
- `thm:class-mertens-explicit` -- Explicit class Mertens theorem under twisted spectral gap
- `thm:class-mertens-fourier` -- Non-abelian Fourier reconstruction of class constants
- `thm:abelian-shadow-defect` + `thm:cyclic-detection-boundary` -- Abelian shadow / non-abelian defect decomposition with exact boundary of cyclic detection

The key new mechanism is that primitive extraction from finite-group extension data requires Adams operations psi^m intertwined with Mobius inversion, not bare Mobius inversion alone. This is a structural observation that appears not to have been made in the Chebotarev literature for SFTs (Parry--Pollicott 1986, Noorani--Parry 1992, Pollicott--Sharp 2007). The quotient functoriality theorem and the abelian-shadow/non-abelian-defect orthogonal splitting give a precise accounting of what cyclic data can and cannot detect.

The S3-example (`cor:s3-example-profile`) provides a concrete demonstration: the sign trace channel vanishes identically (L_eps = 0), yet Pi_eps(1/2) is nonzero. The non-abelian defect energy is 4.4x the abelian shadow energy. This is a genuine phenomenon invisible to periodic-level counting.

**ETDS fit**: Chebotarev-type results for shifts are a recognised ETDS topic (the Parry--Pollicott 1986 paper was published in ETDS). The non-abelian upgrade via Adams operations and the shadow/defect decomposition are genuinely new content.

---

## 2. Scope cuts -- what does not belong

Three sections present in the directory are correctly excluded from main.tex:

### sec_syntax_zeta.tex (DFA density dichotomy, Zeckendorf languages)

**Cut rationale**: The DFA density dichotomy (Theorem 5.1) is a clean finite-automata result but addresses computability/complexity rather than ergodic theory. The Zeckendorf non-regularity corollary is cute but peripheral. ETDS referees would view this as a digression. This material belongs in a separate note (perhaps for a computability or combinatorics journal) or in a survey.

### sec_operator.tex (Fredholm--Witt bridge, cyclic-block realisation, CLT)

**Cut rationale**: The Fredholm--Witt bridge (Theorem 6.1) is a useful conceptual frame (trace-class generalisation of the Euler product) but does not carry new information beyond the finite-state case treated in the main paper. The cyclic-block Fredholm realisation is a converse-direction existence result. The spectral-gap CLT (Theorem 6.3) is classical (Nagaev--Guivarch). Including these would dilute focus without strengthening the main narrative.

### sec_online_kernel.tex (10-state synchronisation kernel)

**Cut rationale**: The synchronisation kernel analysis is a concrete worked example: 10x10 matrix, completed determinant on a genus-6 curve, cyclotomic resultants, asymptotic expansion of twisted Perron roots. While mathematically solid, it is too specialised and too long for the ETDS submission. It can be published separately or as a companion paper. The genus computation and Galois group determination, while interesting, are algebraic geometry rather than dynamical systems.

### Additional items to consider cutting

- **Appendix C (rigidity for growing families)**: `thm:finite-part-residue-drift-trichotomy` is a clean result but addresses asymptotic families rather than fixed SFTs. It could be flagged as a remark or removed if page count is an issue. Current length is moderate (< 2 pages equivalent), so retaining it is acceptable.

- **Appendix B (Dirichlet characters, Gauss sums)**: This section translates cyclic reconstruction into number-theoretic language. It is well-integrated with the main story but is the most "number-theoretic" part of the paper. An ETDS referee might view it as tangential. Consider condensing to the key statement (`thm:finite-part-dirichlet-character-inversion-prime`) plus the growth criterion (`cor:finite-part-near-rh-q-axis-envelope`).

---

## 3. Gap analysis -- missing proof steps

### Gap 1: Twisted spectral-gap hypothesis

**Location**: `thm:class-mertens-explicit` assumes eta = max_{rho != 1} rho(A_rho) < lambda.

**Status**: The hypothesis is stated explicitly and its role is carefully delineated in Remark 4.14 (`rem:twisted-spectral-gap-role`). The paper correctly notes that the determinant identities and Adams--Mobius inversion hold without this hypothesis; it is needed only for Perron-point evaluation.

**Gap**: The paper does not provide dynamical criteria that guarantee eta < lambda for broad classes of cocycles. This is flagged as an open problem in the conclusion. For ETDS, this is acceptable: the analogous hypothesis in the original Parry--Pollicott Chebotarev paper was also assumed rather than derived. However, it would strengthen the paper to add a brief discussion of known sufficient conditions (e.g., the rapid-mixing criterion of Boyle--Schmieding, or explicit verification for the S3-example).

**Recommendation**: Add 2--3 lines to Remark 4.14 citing known sufficient conditions. Verify eta < lambda explicitly for the S3-example (this should follow from rho(A_rho) = 1 < 2 = lambda since chi_{A_rho}(t) = t^3(t+1) gives rho(A_rho) = 1).

### Gap 2: Adams decomposition for general finite groups

**Location**: `lem:adams-coefficients-bounded` and its use in `cor:primitive-peter-weyl-determinant`.

**Status**: The Adams decomposition coefficients a_{rho,sigma}^{(m)} are defined abstractly. For the S3-example they are computed explicitly.

**Gap**: The paper does not provide a general formula or algorithm for a_{rho,sigma}^{(m)} beyond the bound |a_{rho,sigma}^{(m)}| <= (dim rho)^2. For dihedral groups, symmetric groups, or other specific families, explicit formulas could be given.

**Recommendation**: This is not a mathematical gap (the coefficients are well-defined representation-theoretic quantities). No action needed for ETDS, but a remark noting that standard character-table methods compute these coefficients would be helpful.

### Gap 3: Uniqueness aspects of the finite-part formula

**Location**: `thm:finite-part-primitive-closed-form`.

**Status**: The formula gives FP(A) in two equivalent forms. It does not address whether FP(A) determines A (clearly it does not, since dim-1 matrices have FP = 0 regardless of lambda).

**Gap**: The paper does not discuss to what extent FP(A) is a new spectral invariant independent of C(A) and the primitive orbit counts separately.

**Recommendation**: Add a sentence to the discussion noting that FP(A) packages C(A) and the primitive orbit tail into a single quantity, and that the gap Gap(A) = log C(A) - FP(A) > 0 already provides non-trivial content. This is addressed implicitly by `cor:finite-part-gap-positive` but could be stated more explicitly.

### Gap 4: Completeness of the S3-example

**Location**: `prop:s3-example-channels`, `prop:s3-example-primitive-channels`, `cor:s3-example-profile`.

**Status**: The S3-example is fully computed, with explicit numerical values for Pi_eps(1/2) and Pi_rho(1/2).

**Gap**: The numerical values are stated to specific decimal digits but no rigorous error bound is given for the truncated series computation. The series are absolutely convergent with explicit geometric bounds, so this is straightforward to address.

**Recommendation**: Add a brief remark noting that the series converge geometrically with ratio at most Lambda_rel^2 = (1/2)^2 = 1/4, so the first K terms give K decimal digits of accuracy. No formal verification script is provided -- consider adding one per the Omega research charter's reproducibility requirement.

### Gap 5: No formal verification script

**Status**: The paper contains no Python script for the S3-example computations. The Omega research charter requires all numerical results to be reproducible by script.

**Recommendation**: Create a Python script that computes the S3 twisted matrices, verifies the characteristic polynomials, and evaluates Pi_eps(1/2) and Pi_rho(1/2) to the stated precision. This is a P3/P4 task but should be flagged now.

---

## 4. Sharpened theorem lineup for ETDS

Based on the analysis above, the recommended theorem lineup for the ETDS submission is:

### Tier 1: Flagship results (must appear prominently)

1. **Finite-part primitive formula** (`thm:finite-part-primitive-closed-form`): This is the paper's raison d'etre. Cleanly stated, cleanly proved.

2. **Cyclic single-layer reconstruction** (`thm:finite-part-cyclic-lift-single-q-torsion-reconstruction`): Sharp threshold q >= d for one-shot spectral reconstruction. Elegant DFT argument.

3. **Adams--Mobius primitive inversion** (`cor:class-function-adams-mobius`): The key new mechanism for the non-abelian part. This is what distinguishes the paper from bare Chebotarev.

4. **Class Mertens theorem** (`thm:class-mertens-explicit`): The quantitative payoff of the determinant calculus. Explicit error terms under twisted spectral gap.

5. **Abelian shadow / non-abelian defect** (`thm:abelian-shadow-defect` + `thm:cyclic-detection-boundary`): The structural decomposition. Clean orthogonal splitting. Identifies the exact frontier of cyclic detection.

### Tier 2: Supporting results (essential for completeness)

6. **Orbit-Mertens asymptotic** (`cor:finite-part-mertens-asymptotic`): Connects FP(A) to Mertens' theorem.

7. **Cyclic-lift closed form** (`thm:finite-part-cyclic-lift-reduced-constant-closed`): Foundation for cyclic reconstruction.

8. **Quotient functoriality** (`thm:quotient-functoriality`): Makes the abelian-shadow identification rigorous.

9. **Non-abelian Fourier reconstruction** (`thm:class-mertens-fourier`): Fourier inversion on class functions. Plancherel identity.

10. **Quadratic Adams obstruction** (`thm:quadratic-adams-obstruction`): Explains the S3 phenomenon at the structural level.

### Tier 3: Appendix results (retain for depth, can be condensed)

11. **Holomorphic variation** (`thm:logM-holomorphic-variation`): Shows FP varies analytically in families. Important for applications.

12. **Truncation bound** (`thm:logM-truncation-bound`): Effective computation.

13. **Boundary multiplicities** (`thm:finite-part-boundary-multiplicity-qaxis-energy`): Cesaro recovery of boundary spectrum. Nice result.

14. **Growing-family rigidity** (`thm:finite-part-residue-drift-trichotomy`): Clean asymptotic-family statement. Keep if space permits.

### Recommended cuts within the current paper

- The Parseval/aliasing material (`thm:finite-part-nyquist-parseval-aliasing`) could be condensed to a remark.
- The Galois covariance proposition (`prop:finite-part-torsion-table-galois-covariance`) and rationality criterion (`cor:finite-part-torsion-table-galois-certificate`) are algebraically nice but could move to an addendum.
- The Dirichlet series `thm:finite-part-cyclic-lift-polylog-dirichlet-xi` is a reformulation rather than a new result; consider condensing.

### Page estimate

With the current structure (Sections 1--5 + 3 appendix sections + references), the paper is approximately 45--50 pages in amsart 11pt format. ETDS papers in this range are common (the Boyle--Schmieding 2017 paper is 34 journal pages). The appendix material could be trimmed to bring the total under 40 pages if needed.

---

## 5. Assessment for ETDS

**Strengths for ETDS**:
- The paper addresses a classical object (dynamical zeta function for SFT) with a new invariant (finite-part constant) and a new mechanism (Adams--Mobius primitive inversion).
- The abelian/non-abelian bridge is well-executed: cyclic reconstruction and finite-group extensions are treated as two facets of one framework.
- The S3-example is a concrete, computable demonstration of a genuinely non-abelian phenomenon.
- The writing is technically clean, with full proofs and explicit error terms.

**Risks for ETDS**:
- The paper is long. A referee might ask for condensation.
- The appendix material (Dirichlet characters, growing families) pulls toward analytic number theory. An ETDS referee might suggest removing this.
- The twisted spectral-gap hypothesis is assumed rather than established for broad classes.

**Overall**: The paper is competitive for ETDS. The finite-part formula and cyclic reconstruction are clean, new, and well-motivated. The non-abelian package (Adams--Mobius, class Mertens, shadow/defect) is the strongest selling point and goes beyond existing Chebotarev literature. Recommendation: submit after addressing Gaps 1 and 5 above.

---



# P3 Journal-Fit Rewrite Note: ETDS

**Date**: 2026-03-30
**Target journal**: Ergodic Theory and Dynamical Systems (ETDS)
**Paper direction**: H

---

## Changes made

### 1. Abstract (main.tex)

Rewritten to ~150 words. Changes:
- Opens with the subshift of finite type and primitive adjacency matrix (ETDS context).
- States the three main contributions concisely: finite-part formula, cyclic reconstruction, Adams--Mobius primitive inversion.
- Removes the displayed equations (inappropriate length for ETDS abstracts).
- Mentions the S3-example as a concrete result, not a summary paragraph.
- Removes the closing "manifesto" sentence ("Thus cyclic lifts and finite-group extensions become...").

### 2. Introduction (sec_introduction.tex)

Fully rewritten to follow ETDS conventions:
- Opens with the mathematical context: dynamical zeta-functions, Bowen--Lanford, Manning, Ruelle, Parry--Pollicott, Baladi.
- Main results stated as Theorem A, Theorem B, Theorem C (standard ETDS style for the introduction).
- Theorem A: Finite-part formula at the Perron pole, including the Mertens asymptotic.
- Theorem B: Cyclic reconstruction of the reduced spectrum, with all three parts (full sequence, one layer, exponential fingerprint).
- Theorem C: Primitive determinant calculus for finite-group extensions, with three clearly labelled parts (Adams--Mobius inversion, class Mertens constants, quotient functoriality).
- Connection to the ETDS tradition is made explicit throughout: Parry--Pollicott 1986 (published in ETDS), Boyle--Schmieding 2017 (published in ETDS), Ruelle's programme, Baladi's transfer-operator theory.
- Added citation to Lind--Marcus 1995 for inverse spectral context.
- Added citation to Baladi 2000 for transfer-operator context.
- "What is standard and what is new" section replaced with "Relation to existing work" -- same comparison table but with neutral headers ("What is proved here" instead of "New theorem-level input").
- "Organisation" section renamed to "Plan of the paper" and references concrete theorem labels (Theorem A, Theorem B).
- Removed the sentence "Accordingly, the finite-group part of the paper is not another Chebotarev statement in disguise. Its novelty lies in..." -- promotional language.

### 3. Conclusion (sec_conclusion.tex)

Expanded from 25 lines to 72 lines with proper ETDS-style discussion:
- Subsection "Summary of the main contributions" -- concise recap referencing theorem labels.
- Subsection "Open problems" with three specific problems:
  1. Dynamical criteria for the twisted spectral gap (connects to Parry--Pollicott 1986 and Boyle--Schmieding 2017).
  2. Non-abelian analogues of the arithmetic appendix.
  3. Transfer-operator extensions (connects to Baladi, Ruelle--Pollicott resonances, countable-state shifts).
- This gives ETDS readers clear next directions and ties the paper to the broader dynamical-systems programme.

### 4. Bibliography (references.bib)

- Removed 15 uncited entries: CuntzKrieger1980, DemboZeitouni2010LargeDeviations, BrinStuck2002, Karp1978MinCycleMean, Ziemian1995RotationSFT, ChazottesGambaudoUgalde2011ZeroTempLocConst, LevinPeresWilmer2009MarkovMixing, MorseHedlund1940, Zeckendorf1972, WaltersErgodicTheory, Kitchens1998, Bowen1975EquilStates, SkolemMahlerLech, Parry1964Intrinsic.
- Retained all 15 entries that are actually cited in the included .tex files.
- Kept Baladi2000PositiveTransfer (now cited in intro and conclusion).
- Kept LindMarcus1995 (now cited in intro for inverse spectral context).
- Final count: 15 entries, all cited.

### 5. Style pass

- sec_chebotarev.tex: Changed "The genuinely new ingredient begins when the determinant data are pushed..." to "The specific content of the present paper begins when the determinant data are pushed..." (line 101).
- sec_appendices.tex: Removed informal/chatty appendix openers:
  - "The results collected here are technically useful but are no longer part of the main narrative." -> neutral opening.
  - "This appendix gathers the arithmetic consequences of the cyclic reconstruction theorem that were removed from the main text in order to keep the principal abelian spine short." -> removed revision-trace language ("removed from the main text").
  - "The final appendix records the growing-family statements that are downstream from the cyclic reconstruction machinery but are not needed for the core finite-part / finite-group bridge developed in the main text." -> neutral opening.
- No AI-voice issues (novel framework, paradigm shift, groundbreaking, etc.) were found in any included file.
- No revision-trace language was found in any .tex file.

### 6. File length check

All .tex files are under 800 lines:
- main.tex: 100
- sec_introduction.tex: 276
- sec_preliminaries.tex: 194
- sec_finite_part.tex: 418
- sec_chebotarev.tex: 619
- sec_shadows.tex: 653
- sec_conclusion.tex: 72
- sec_appendices.tex: 718 (three appendix sections; largest included file, still under limit)

No splits needed.

---

## Items NOT changed (deliberate)

- sec_preliminaries.tex: Clean, standard notation section. No changes needed.
- sec_finite_part.tex: Proofs are self-contained and cleanly written. No style issues found.
- sec_chebotarev.tex: One minor style fix (above). Otherwise clean.
- sec_shadows.tex: Clean. The S3-example is well-presented. "Genuinely non-abelian" language in the section opener is standard mathematical usage (describing the content of the orthogonal complement), not promotional.
- sec_appendices.tex: Three minor opener fixes (above). Otherwise clean.
- Excluded files (sec_syntax_zeta.tex, sec_operator.tex, sec_online_kernel.tex): Not touched, as they are excluded from main.tex.

---



# P4 Editorial Review 2026-03-30

**Paper**: H -- Dynamical zeta-Function Finite Part and Spectral Fingerprint  
**Journal lens**: ETDS referee / editorial polish pass  
**Decision**: PASS TO P5

---

## Decision

From an ETDS referee perspective, the manuscript is now coherent enough
to pass a P4 editorial-review gate. The introduction states a clean
theorem package, the finite-part and finite-group sections match the
advertised claims, and the \(S_3\) example reads as a genuine worked
example rather than as an informal add-on.

I do **not** see a remaining P4-level blocker that would justify
holding the paper back from an internal P5 review. The main remaining
risks are either submission-metadata issues or reproducibility issues
that are outside a pure editorial-polish pass.

---

## Evidence Checked

- Existing local build artifacts indicate a clean compiled manuscript:
  `main.pdf` is 36 pages, with no undefined references.
- Remaining TeX warnings are typographic only:
  small underfull/overfull box warnings, concentrated in the
  introduction comparison table and a few displayed numeric lines in the
  \(S_3\) section.
- The page budget is currently acceptable for ETDS; Appendix B is no
  longer a length blocker at the present 36-page size.

---

## Editorial Findings

### Blockers

- None for P4.

### Must-fix

- None remaining after this pass.

### Should-fix / Watchlist

1. `main.tex` still contains placeholder submission metadata:
   `[Author]`, `[Affiliation]`, `[email]`. This is not a P4 blocker, but
   it is a real P7 submission blocker.
2. The numerical constants in the \(S_3\) example are stated as final
   decimal values without a paper-local verification script. The proof
   chain is mathematically self-contained, so this is not a P4 blocker,
   but it remains a P5/P7 reproducibility risk.
3. If ETDS later requests further compression, Appendix B
   (`app:arithmetic`) is still the first place to shorten. At the
   current 36-page length, however, I would not cut it pre-emptively.
4. The introduction comparison table still produces minor box warnings.
   This is typographic, not structural.

---

## Small Fixes Applied In This Pass

1. Expanded the remark on the twisted spectral-gap hypothesis in
   `sec_chebotarev.tex` so the role of `eta < lambda` is framed more
   naturally for ETDS readers and explicitly tied to the existing
   ETDS-facing literature.
2. Added an explicit `eta < lambda` verification to the \(S_3\) worked
   example in `sec_shadows.tex`, so the example now certifies the
   hypothesis of the class-Mertens theorem in-text instead of leaving it
   implicit.

---

## Recommendation For Next Stage

- Advance the paper to P5 internal review.
- Do not spend more time on broad stylistic rewriting unless a later
  review finds a concrete mathematical or structural issue.
- Before P7, fill in submission metadata and decide whether the \(S_3\)
  decimal evaluations need a paper-local reproducibility artifact.

---


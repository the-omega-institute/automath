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

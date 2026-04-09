# P4 Editorial Review -- Gate 3 (Claude Final Review)

**Paper:** Cayley--Chebyshev Mode Calculus, Poisson Entropy Asymptotics, and Cardinal Reconstruction in a Strip RKHS

**Target:** Journal of Functional Analysis (JFA)

**Date:** 2026-04-03

**Reviewer:** Claude Gate 3

---

## 1. Decision

**MINOR_REVISION**

---

## 2. ChatGPT BLOCKER Verdicts

### I1: Bibliography missing, [?] placeholders throughout

**VERDICT: PARTIALLY**

The `references.bib` file is complete and contains all 27 cited entries. Every `\cite{}` key in the `.tex` sources has a matching bib entry. There are zero `[?]` in the LaTeX source itself. The problem is that bibtex was never run during the compilation step, so the compiled PDF shows `[?]` for all citations. This is a build-process issue, not a content issue. A single `pdflatex + bibtex + pdflatex + pdflatex` cycle will resolve it completely.

**Fix:** Run the full LaTeX build chain. No content changes needed.

### I2: Section 7 not positioned against Lorentzian/Cauchy shift literature

**VERDICT: DISMISSED**

The current draft contains an explicit positioning paragraph (sec_strip_lattice.tex, lines 215--233) that:
- Cites the standard SIS framework (de Boor--DeVore--Ron, Ron--Shen, Bownik, Aldroubi--Grochenig, Grochenig--Romero--Stockler).
- Explicitly acknowledges the prior Cauchy/Lorentz integer-shift literature (Kiselev--Minin--Novikov 2016, 2019).
- States clearly what is new (Poisson-strip realization, closed lattice symbol, exact cardinal Fourier formula and norm formula).

There is a second remark (lines 527--546) reinforcing the same positioning. The introduction (lines 120--139) also contains a detailed prior-work paragraph covering the same material. This blocker was either raised against an earlier draft or is incorrect.

### I3: Theorem 5.8 asymptotic bookkeeping inconsistent

**VERDICT: DISMISSED**

I independently verified every coefficient in the eighth-order expansion (Theorem `poisson-kl-eighth`, eq. 5.9) by:
1. Verifying all 10 appendix integrals against the Chebyshev--Fourier expansions using exact arithmetic.
2. Assembling the $t^{-4}$, $t^{-6}$, and $t^{-8}$ coefficients from the multinomial expansion of $\Phi(\delta_t)$.
3. Checking that the two groups in the $t^{-8}$ term match the claimed decomposition.

All coefficients are correct. The $\Phi$ series $\Phi(z) = \sum_{k\ge 2} (-1)^k/(k(k-1)) z^k$ is standard and verified. The uniform remainder from Proposition `cayley-mode-remainder` (bounded $v_N$) justifies the term-by-term integration. The moment hypotheses (finite seventh absolute moment) are sufficient for the $O(t^{-7})$ uniform remainder in $\delta_t$.

### I4: Theorem 5.9 displayed expansions false pointwise

**VERDICT: DISMISSED**

I verified every algebraic identity in Theorem `poisson-defect-ladder` (Theorem 5.9):
1. The identity $(64/\sigma^6)C_6 = -7 - 2\beta_3^2 - 8\kappa$ follows from $\kappa = \beta_4 - 1 - \beta_3^2$ and the eighth-order formula.
2. The substitution $P_8 = 3 - 12\beta_4 + 9\beta_3^2 + 12\beta_6 - 30\beta_3\beta_5 + 20\beta_4^2$ matches $(256/\sigma^8)C_8$.
3. Expanding $P_8$ in $(\kappa, \beta_3, L, M)$ gives $23 + 20\kappa^2 + 16\beta_3^2\kappa + 64\kappa + 2\beta_3^4 + 13\beta_3^2 + 6\beta_3 L + 12M$ -- verified term-by-term.
4. The $\|Q_3\|^2$ substitution identity checks: $12\|Q_3\|^2 + 32\kappa^2 + (61/4)\beta_3^2\kappa + 52\kappa + 2\beta_3^4 + 13\beta_3^2 = P_8 - 23 + 12M + 6\beta_3 L$ recombines correctly.
5. The equality characterization ($\beta_3 = 0$, $\kappa = 0$ forces the symmetric two-point law) is correct.

No displayed expansion is false, neither pointwise nor in the integrated sense. The "pointwise" objection appears to be a misreading; the paper never claims pointwise convergence of the entropy expansion -- it is an asymptotic expansion of the integrated KL divergence.

---

## 3. New Issues Found

### N1 (Minor): Display error in proof of Theorem 5.8, line 486

**Location:** sec_entropy_asymptotics.tex, line 486

**Problem:** The displayed coefficient of $t^{-7}$ in $-(1/6)\delta_t^3$ is written as $+a_2^2 a_3 / t^7$. The correct value is $-(1/2)a_2^2 a_3 / t^7$, since the multinomial coefficient gives $3$ orderings and $-(1/6) \times 3 = -(1/2)$.

**Impact:** None. Line 490 explicitly states that all odd-order terms integrate to zero by Lemma `mode-parity-vanish`. The final formula (eq. 5.9) is correct. This is a cosmetic error in an intermediate display.

**Fix:** Replace `+a_2^2 a_3 / t^7` with `-(1/2)a_2^2 a_3 / t^7` on line 486 (inside the display for $-(1/6)\delta_t^3$).

### N2 (Minor): Build chain not completed

**Location:** Build process (no `.bbl` file exists)

**Problem:** The PDF was compiled with `pdflatex` alone. No `bibtex` pass was ever run, so all citations appear as `[?]` in the compiled output and cross-reference labels may be unstable.

**Fix:** Run `pdflatex main && bibtex main && pdflatex main && pdflatex main`.

### N3 (Cosmetic): Empty author field

**Location:** main.tex, line 46

**Problem:** `\author{}` is empty.

**Fix:** Fill in before submission.

### N4 (Minor): Toscani2015 bib entry has year mismatch

**Location:** references.bib, line 262--271

**Problem:** The bib key is `Toscani2015` but the `year` field says `2016`. The paper was published in 2016 (DOI confirms). The key should match or be updated for consistency.

**Fix:** Either rename the key to `Toscani2016a` (and update all `\cite` calls) or leave as-is (the compiled output uses the year from the `year` field, not the key). Low priority.

---

## 4. Mathematical Correctness Assessment

### Theorems verified correct:

| Theorem | Verification method |
|---|---|
| `haar-pullback-uniqueness` | Elementary ODE + boundary conditions; proof is watertight |
| `precision-ledger` | Standard change-of-variables identity |
| `cayley-chebyshev-mode` | Chebyshev generating function verified; explicit modes $u_2$--$u_6$ confirmed |
| `poisson-kl-even-orders` | Parity argument via mode cancellation lemma; structurally sound |
| `poisson-kl-eighth` | All 10 appendix integrals verified by exact arithmetic; all coefficients confirmed |
| `poisson-defect-ladder` | Full algebraic expansion verified independently |
| `poisson-defect-amplification` | Follows from ladder by direct subtraction; checked |
| `poisson-defect-stability` | Key inequality $|x-\mathrm{sgn}(x)| \le |x^2-1|$ verified; W2 coupling correct |
| `mode-gram-kernel` | Residue computation verified numerically to machine precision |
| `mode-space-rkhs` | Density argument (Poisson regularization + Fourier injectivity) is rigorous |
| `gram-space-poisson-image` | RKHS norm via Fourier reproducing property verified |
| `poisson-hardy-splitting` | Standard Fourier half-line decomposition |
| `poisson-lattice-sampling` | Lattice symbol verified; Riesz bounds from symbol bounds; sampling inequality from Toeplitz algebra |
| `poisson-cardinal-reconstruction` | Cardinal kernel from Toeplitz inversion; norm formula from symbol |
| `poisson-central-two-channel` | Laplace identity verified; Fubini justified |

### No unstated assumptions found.

All hypotheses are explicit. The moment conditions (finite seventh moment for eighth-order expansion, finite fourth moment for second-order approximation) are stated in each theorem.

### Novelty assessment:

The paper is not a repackaging of known results. The genuinely new contributions are:
1. The Cayley--Chebyshev mode calculus connecting Chebyshev polynomials of the second kind to the Poisson comparison kernel.
2. The even-order vanishing principle for KL divergence coefficients, derived from the mode parity.
3. The explicit eighth-order expansion with defect coordinates and the amplification inequality $\Delta_8 \ge (13\sigma^2/8)\Delta_6$.
4. The identification of the Gram kernel RKHS with a Poisson image space and its strip extension.
5. The closed-form lattice symbol, cardinal kernel Fourier formula, and exact interpolant norm.

Items 1--3 are new entropy-rigidity results with no close precedent. Items 4--5 apply known SIS/RKHS machinery to a new kernel, yielding a fully explicit Cauchy/Poisson analogue of recent Gaussian lattice theory.

---

## 5. Editorial Assessment

### Abstract vs. content: MATCH

The abstract accurately describes all results proved in the paper. No overclaiming.

### Introduction: GOOD

Reader-friendly for JFA audience. Clear statement of main results with theorem references. Prior work is positioned in two well-organized paragraphs covering entropy literature and SIS/RKHS literature. The structural roadmap at the end is clear.

### Structure: SOUND

The section ordering is logical: Cayley formulas -> Haar pullback -> entropy asymptotics (the analytic core) -> Gram space and RKHS -> strip model and lattice reconstruction. The appendix properly isolates the computational integrals.

### Bibliography: ADEQUATE

27 entries, all cited, no orphans. Coverage includes classical references (Stein--Weiss, Rudin, Duren, Aronszajn), the relevant entropic CLT literature (Barron, Bobkov--Chistyakov--Gotze, Toscani), and the SIS/sampling literature (de Boor--DeVore--Ron through Romero--Ulanovskii--Zlotnikov 2024). The Kiselev--Minin--Novikov references address Cauchy/Lorentz shifts specifically. No major gaps.

---

## 6. Summary

| ChatGPT Blocker | Verdict | Action needed |
|---|---|---|
| I1: Bibliography missing | PARTIALLY (build issue, not content) | Run bibtex |
| I2: Section 7 positioning | DISMISSED (positioning is present) | None |
| I3: Theorem 5.8 bookkeeping | DISMISSED (all coefficients verified correct) | None |
| I4: Theorem 5.9 false pointwise | DISMISSED (all identities verified correct) | None |

| New Issue | Severity | Action needed |
|---|---|---|
| N1: Line 486 display error | Minor | Fix coefficient sign/value |
| N2: No bibtex run | Minor | Run build chain |
| N3: Empty author | Cosmetic | Fill before submission |
| N4: Bib key year mismatch | Cosmetic | Optional rename |

**Bottom line:** The mathematics is correct throughout. The ChatGPT Gate 1 BLOCKERs were either targeting an earlier draft version (I1 partially, I2 fully) or were mathematically wrong (I3, I4). The paper needs two targeted fixes (one display typo, one build step) and is otherwise ready for submission.

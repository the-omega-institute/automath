# P4 Editorial Review -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Title: *Finite-Window Zeckendorf Fibers and the Discrete Thermodynamics of Fibonacci Partition Differences*
Target journal: Transactions of the American Mathematical Society (TAMS)
Reviewer role: Handling editor / senior referee

---

## 1. Decision

**MINOR_REVISION**

The paper presents a coherent and substantial contribution to combinatorial number theory: it identifies finite-window Zeckendorf fiber multiplicities with Fibonacci-lag discrete derivatives of the classical partition function, transfers the moment growth to Sanna's partition constants via a finite-state realization, builds a complete discrete thermodynamic formalism (pressure, canonical/microcanonical bands, zero-temperature limit), and certifies arithmetic content (full symmetric Galois groups, linear disjointness, Chebotarev product densities) in the window $q = 9, \ldots, 17$. The escalation ladder is well-structured, the proofs are complete within the stated scope, and the scope exclusions are properly flagged. The issues identified below are all correctable without restructuring the paper.

---

## 2. Mathematical assessment

### 2.1 Are the 10 main theorems correctly stated?

All 10 main results are correctly stated. Detailed audit:

| # | Result | Verdict |
|---|--------|---------|
| A | Partition-difference formula (`thm:partition-difference`) | Correct. The generating-function factorization and the range argument ($0 \le n < F_{m+2}$ ensures only the factor $(1 + z^{F_{m+1}})$ contributes) are clean. |
| B | Fibonacci-window sandwich + all-$q$ transfer (`thm:fibonacci-window-sandwich`, `thm:all-q-transfer`) | Correct. The lower bound uses the identity $a_m(n) = R^\dagger(n)$ for $n < F_{m+1}$; the upper bound uses $a_m(n) \le R^\dagger(n)$. The transfer to Sanna's constants via the pointwise bound $R(n) \le R^\dagger(n) \le 2 \max\{R(n), R(n-1)\}$ is valid. |
| C | Collision kernel + algebraicity + pressure convexity (`thm:collision-kernel`, `thm:symmetric-compression`, `cor:lambda-algebraic`, `thm:global-pressure-convexity`) | Correct. The finite-state realization is rigorous, with the transducer construction spelled out in Appendix A. The symmetric compression via histogram states is standard. Pressure convexity follows from Holder's inequality applied to the fiber multiplicities. |
| D | Gibbs selection (`thm:gibbs-selection`) | Correct. The moment-ratio tilting argument is standard and the two-sided exponential concentration follows cleanly. |
| E | Microcanonical band bounds (`thm:microcanonical-bands`) | Correct. The cardinality and visible-mass bounds follow by combining the Gibbs concentration with pointwise bounds on $d_m(x)^q$ within the band. |
| F | Zero-temperature law (`thm:max-fiber`, `thm:diagonal-high-moments`, `thm:zero-temp-concentration`) | Correct. The squeeze $D_m^q \le S_q(m) \le F_{m+2} D_m^q$ combined with the $q \to \infty$ limit of $\lambda_q^{1/q}$ is standard. |
| 7 | Renyi entropy-rate spectrum (`thm:renyi-entropy-rate`) | Correct. Direct consequence of the moment asymptotics divided by $2^{mq}$. |
| 8 | Collision entropy rate + alternating correction (`thm:collision-entropy-rate`, `thm:q2-alternating-second-order`) | Correct. The cubic recurrence proof via the auxiliary quantity $U_m = B_m(F_{m+1})$ is verified step by step. The root analysis of $\lambda^3 - 2\lambda^2 - 2\lambda + 2$ is correct; the contradiction argument for $c_- \neq 0$ is valid. |
| 9 | Galois groups $\cong S_{d_q}$ (`thm:galois-sd-window`) | Correct, conditional on the certificate tables. The proof chain -- irreducibility via Gauss's lemma from a mod-$p$ irreducibility certificate, primitivity from an $(n-1)$-cycle, fullness from Jordan's theorem using a prime cycle of length $\le d_q - 3$ -- is clean and standard. |
| 10 | Linear disjointness + Chebotarev product (`thm:linear-disjointness`, `cor:chebotarev-product`) | Correct. The squareclass independence argument via the $4 \times 4$ Legendre symbol matrix is valid. The normal-subgroup argument for the intersection being trivial is standard. |

### 2.2 Are proofs complete? Any hidden assumptions?

All proofs in the main line are complete. The dependency structure is clean:

- Theorems A--B depend only on the definition of the fold, Zeckendorf's theorem, d'Ocagne's identity, and Sanna's theorem (which is cited as an external result with a precise reference).
- Theorems C--F depend on Perron--Frobenius theory for nonneg. integer matrices and the transducer construction in Appendix A. Both are self-contained.
- The Galois results depend on the exact integer recurrence data in Appendix B (Table B.1). This is a computational input, but its provenance is explicitly documented.

**One implicit assumption to flag**: The proof of `thm:collision-kernel` (line 49-70 of `sec_moment_kernel.tex`) delegates the full construction to Appendix A and states the result for $m \ge m_0(q)$ with a "finite offset." However, `prop:appendix-collision-automaton` in the appendix proves the identity for $m \ge 0$ (line 156: "for every $m \ge 0$"). The main-text statement is therefore more conservative than what is actually proved. This is not an error but is mildly confusing -- the main text should either match the appendix or explain the discrepancy.

### 2.3 Is the certified arithmetic window accurately bounded?

Yes. The boundaries are sharp and properly stated:

- **Certified range**: $q = 9, \ldots, 17$ for Galois groups $S_{d_q}$; degree sequence $(7, 9, 9, 13, 11, 13, 11, 13, 13)$.
- **Linear disjointness**: certified only for the block $q \in \{12, 13, 14, 15\}$.
- **Product Chebotarev density**: $1/(13 \cdot 11 \cdot 13 \cdot 11) = 1/20449$.
- The quadratic case ($q = 2$) has a complete explicit treatment via the cubic $\lambda^3 - 2\lambda^2 - 2\lambda + 2$.
- The gap $q = 3, \ldots, 8$ is covered by the general transfer theorem ($S_q \asymp \lambda_q^m$) but has no per-$q$ polynomial data. This is not stated explicitly in the manuscript body (only in the P2 note). A brief remark acknowledging this gap would strengthen the presentation.

### 2.4 Are scope exclusions properly flagged?

Yes, with appropriate care:

- $q \ge 18$: flagged in `sec_conclusion.tex` ("Extension of these arithmetic certificates beyond $q = 17$ ... remain open") and in `rem:q16q17`.
- Secondary spectral pattern: explicitly labeled as "audited descriptive fingerprints rather than symbolic isolation intervals" in `rem:secondary-spectral-pattern`.
- Squareclass independence beyond $\{12, 13, 14, 15\}$: flagged in `rem:q16q17`.

---

## 3. Editorial assessment

### 3.1 Abstract-introduction-theorem arc

The arc reads well for TAMS. The abstract is dense but precise (~170 words), covering the partition-difference identity, moment transfer, finite-state realization, pressure geometry, and arithmetic payoff. The introduction correctly previews all six named theorems and the arithmetic window. The escalation paragraph (lines 89-96 of `sec_introduction.tex`) efficiently summarizes the logical flow.

**Minor issue**: The abstract mentions "two-sided exponential estimates for band cardinality and visible mass" (Theorem E) but does not state the exponents. This is acceptable for an abstract but could be strengthened.

### 3.2 Escalation ladder

The escalation is clear and well-paced:

1. Fibers $\to$ partition differences (Section 3)
2. Differences $\to$ moment transfer via Fibonacci windows (Section 4)
3. Moments $\to$ finite-state matrix realization, pressure geometry (Section 5)
4. Pressure $\to$ canonical/microcanonical concentration (Section 5, cont.)
5. Concentration $\to$ zero-temperature, Renyi spectrum (Sections 5--6)
6. Recurrence polynomials $\to$ Galois groups, Chebotarev (Section 7)

The quadratic case ($q = 2$, Section 4.3) serves well as a concrete illustration before the general formalism.

### 3.3 Bibliography

The bibliography contains 13 entries, all cited. The references are appropriate:

- Lekkerkerker, Zeckendorf (foundations)
- Chow--Slattery, Chow--Jones, Sanna (direct predecessors)
- Seneta, Lind--Marcus (Perron--Frobenius, symbolic dynamics)
- Frougny (transducer theory)
- Dembo--Zeitouni (large deviations context)
- Cover--Thomas (information theory)
- Dixon--Mortimer (permutation groups / Jordan's theorem)
- Neukirch (Chebotarev density theorem)

This is lean but sufficient for TAMS. No important references appear to be missing.

### 3.4 Appendix proportion

- Appendix A (transducer): 222 lines. Necessary and well-scoped; it makes `thm:collision-kernel` self-contained.
- Appendix B (certification): 176 lines. Necessary for reproducibility of the Galois certificates.

Combined appendix: 398 lines out of ~2700 total included lines (~15%). This is within the acceptable range for TAMS.

### 3.5 Total length estimate

The included .tex files total approximately 2700 lines. Accounting for LaTeX overhead, this corresponds to roughly 35-40 pages in amsart format. This is within TAMS norms for a paper of this scope.

---

## 4. Specific issues

### Issue 1: `remark` theorem style

**Location**: `main.tex`, line 20.
**Problem**: The `remark` environment is declared under `\theoremstyle{plain}`, which gives it the same italic body as theorems and propositions. The AMS convention (and standard `amsart` practice) is to declare remarks under `\theoremstyle{remark}` (upright body, italic header).
**Fix**: Move line 20 after a `\theoremstyle{remark}` declaration:
```latex
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
```

### Issue 2: `thm:collision-kernel` offset discrepancy

**Location**: `sec_moment_kernel.tex`, line 39 ($m \ge m_0(q)$) vs. `sec_appendix_transducer.tex`, line 156 ($m \ge 0$).
**Problem**: The main-text statement introduces an unspecified offset $m_0(q)$ that the appendix proof does not require. This creates a false impression that the identity may fail for small $m$.
**Fix**: Replace $m \ge m_0(q)$ with $m \ge 0$ in `thm:collision-kernel`, matching the appendix proof. If the offset was introduced for a reason not visible in the current text, add a sentence explaining it.

### Issue 3: Definition of $\Delta_q$ overloaded

**Location**: `sec_chebotarev.tex`, line 28 vs. `sec_moment_kernel.tex`, line 248.
**Problem**: In `def:resonance-polynomials` (Section 7), $\Delta_q := n_q - d_q$ is defined as the Hankel codimension. In `def:pressure-slopes` (Section 5), $\Delta_q := P_q - P_{q-1}$ is defined as the pressure slope. Both notations are used extensively in their respective sections. A reader encountering both may be confused.
**Fix**: Rename the Hankel codimension. Suggested: $\delta_q := n_q - d_q$ or $\kappa_q := n_q - d_q$.

### Issue 4: $q$ overloaded in `prop:single-overflow`

**Location**: `sec_preliminaries.tex`, lines 67--68.
**Problem**: The proof of `prop:single-overflow` uses $q$ for the quotient in the division $N_m(\omega) = qF_{m+2} + r$. Throughout the rest of the paper, $q$ is the moment exponent. This local reuse is technically harmless but invites confusion when a reader jumps back to this proposition.
**Fix**: Replace the quotient variable with $b$ (or use the already-defined $b_m(\omega)$ from the same proposition statement).

### Issue 5: Forward reference to appendix table

**Location**: `sec_chebotarev.tex`, line 169 -- "Table~\ref{tab:appendix-recurrences-q9-17}".
**Problem**: This table is defined in `sec_appendix.tex` (Appendix B), which is included after `sec_chebotarev.tex` in `main.tex`. The forward reference resolves in LaTeX after two passes, but it creates a reader-facing issue: the proof of `prop:irreducibility-window` cites a table the reader has not yet seen.
**Fix**: Add a brief parenthetical: "...listed in Table~\ref{tab:appendix-recurrences-q9-17} (Appendix~\ref{app:certification})". This is already partially done for the secondary spectral table; apply the same convention here.

### Issue 6: `cor:visible-band` has a dangling display

**Location**: `sec_ledger.tex`, lines 21--36.
**Problem**: The corollary statement has two display blocks. The first defines $V_m(\varepsilon)$ and the second states the concentration. However, the second display is not syntactically connected to the first -- there is no "Then" or "satisfies" between them. This makes the statement read as two definitions rather than a definition followed by a claim.
**Fix**: Insert "Then" before the second display, e.g.: "Then $p_m(V_m(\varepsilon)) = \ldots$".

### Issue 7: Missing $q = 1$ case in `thm:all-q-transfer`

**Location**: `sec_second_collision.tex`, lines 84--133.
**Problem**: The theorem states $r_q = \lambda_q$ "if $q \ge 2$" using the finite-state kernel. But it also claims $S_q(m) \asymp_q \lambda_q^m$ "for every integer $q \ge 1$." The case $q = 1$ gives $S_1(m) = 2^m$, so $\lambda_1 = 2$. This is consistent but is never explicitly stated. Since $\lambda_1$ enters the pressure sequence ($P_1 = \log 2$) and the Gibbs selection proof, it should be stated.
**Fix**: Add a one-line remark after the theorem: "For $q = 1$, $S_1(m) = 2^m$ gives $\lambda_1 = 2$ directly."

### Issue 8: `cor:log-density-additivity` is redundant

**Location**: `sec_chebotarev.tex`, lines 353--373.
**Problem**: This corollary simply takes the logarithm of `cor:chebotarev-product`. It contains no additional mathematical content. For a TAMS paper, this level of triviality may draw referee criticism.
**Fix**: Demote to a remark or fold into the proof/statement of `cor:chebotarev-product`.

### Issue 9: `cor:renyi-rational-denominator` is tangential

**Location**: `sec_chebotarev.tex`, lines 242--268.
**Problem**: This corollary gives a lower bound on rational denominators of a normalized Renyi-type quantity $D_q$. While technically correct, it is not referenced elsewhere in the paper and its motivation is unclear -- the quantity $D_q$ is defined ad hoc for this single corollary.
**Fix**: Either add a sentence explaining why this bound is of interest (e.g., connection to transcendence conjectures for the pressure slopes) or remove the corollary to tighten the Chebotarev section.

### Issue 10: Appendix ordering in `main.tex`

**Location**: `main.tex`, lines 95--96.
**Problem**: The transducer appendix (Appendix A) is included before the certification appendix (Appendix B), which is the correct logical ordering. However, the `\appendix` command appears on line 94 while the transducer section labels itself as `\section{A bounded-delay transducer model...}`. Under `\appendix`, this will automatically become "Appendix A" and the certification section will become "Appendix B." This is correct but should be verified at compilation time.
**Fix**: No code change needed, but verify at compilation that the appendix numbering is correct.

### Issue 11: No `\thanks` or funding acknowledgment

**Location**: `main.tex`.
**Problem**: TAMS requires an acknowledgment of funding sources and, typically, an author affiliation beyond a project name. "The Omega Project" is not a standard institutional affiliation.
**Fix**: Add `\thanks{}` with appropriate funding/affiliation information before submission. This is an editorial requirement, not a mathematical one.

---

## 5. AI-voice check

The manuscript is clean of AI-voice artifacts. Specifically:

- **No manifesto language**: No sentences of the form "This represents a paradigm shift" or "We provide a comprehensive framework." The claims are local and precisely scoped.
- **No repeated summaries**: The conclusion is 20 lines and does not re-derive the results. The introduction previews but does not re-prove.
- **No loose claims**: Every assertion is either (a) proved in the paper, (b) cited to a specific external reference, or (c) explicitly flagged as numerical descriptive data outside the theorem chain.
- **No hedging filler**: No instances of "it is worth noting that," "interestingly," "remarkably," or similar padding.
- **No revision-trace language**: No "we have improved," "this version corrects," or similar. (P3 rewrite note confirms a style pass was performed.)

**One minor flag**: The phrase "unexpectedly rigid" in `sec_introduction.tex` line 18 is subjective. While common in mathematical writing, a referee might request its removal. Not blocking.

---

## 6. Comparison with P2/P3 notes

### 6.1 P2 decisions -- execution status

| P2 Decision | Status | Notes |
|---|---|---|
| Include `sec_chebotarev.tex` in main line | DONE | Correctly placed between `sec_ledger` and `sec_conclusion` in `main.tex`. |
| Include `sec_appendix.tex` as Appendix B | DONE | Placed after `sec_appendix_transducer.tex` in `main.tex`. |
| Exclude `sec_rewriting.tex` | DONE | Not referenced from `main.tex`. |
| Exclude `sec_appendix_auxiliary.tex` | DONE | Not referenced from `main.tex`. |
| Add Neukirch1999 citation | DONE | Cited in `sec_chebotarev.tex` at `cor:individual-chebotarev` and `cor:chebotarev-product`. |
| Add LindMarcus1995 citation | DONE | Cited in `sec_moment_kernel.tex` preamble and `sec_introduction.tex`. |
| Add CoverThomas2006 citation | DONE | Cited in `sec_ledger.tex` preamble. |
| Add DemboZeitouni2010 citation | DONE | Cited in `sec_moment_kernel.tex` preamble. |
| Remove AhlbachUsatineFrougnyPippenger2013 | DONE | Not in `sec_references.tex`. |
| Remove Kempton2023 | DONE | Not in `sec_references.tex`. |
| Remove ShallitShan2023 | DONE | Not in `sec_references.tex`. |
| Remove BaaderNipkow1998 | DONE | Not in `sec_references.tex`. |
| Abstract mentions Galois/Chebotarev arc | DONE | Abstract closes with the arithmetic window results. |
| Introduction previews full arc | DONE | Escalation paragraph + roadmap in `sec_introduction.tex`. |
| MSC code 11R32 added | DONE | `\subjclass` includes 11R32. |
| Keywords updated | DONE | "Galois groups" and "Chebotarev density" added. |

**All P2 decisions are properly executed.**

### 6.2 P3 rewrite -- did it introduce new problems?

The P3 rewrite was well-executed. The specific issues it may have introduced:

1. **$\Delta_q$ overload** (Issue 3 above): This existed before P3 but became more visible once `sec_chebotarev.tex` was included in the main line. P3 did not introduce it but also did not catch it.

2. **`cor:log-density-additivity` retained** (Issue 8 above): P3 included the full `sec_chebotarev.tex` without trimming this trivial corollary. Minor.

3. **No new mathematical errors**: The P3 rewrite was purely structural (inclusions, bibliography, style). It did not alter any theorem statements or proofs.

4. **File lengths remain under 800 lines**: Confirmed. Largest file: `sec_moment_kernel.tex` at 682 lines.

---

## 7. Summary of required changes

### Must-fix (blocking acceptance)

1. **Issue 3**: Rename $\Delta_q$ in `def:resonance-polynomials` to avoid overloading with the pressure slope.
2. **Issue 1**: Fix `remark` theorem style from `plain` to `remark`.
3. **Issue 11**: Add author affiliation and funding acknowledgment per TAMS requirements.

### Should-fix (strongly recommended)

4. **Issue 2**: Resolve the $m_0(q)$ discrepancy in `thm:collision-kernel`.
5. **Issue 4**: Rename the quotient variable $q$ in `prop:single-overflow`.
6. **Issue 6**: Fix the dangling display in `cor:visible-band`.
7. **Issue 7**: Explicitly state $\lambda_1 = 2$ after `thm:all-q-transfer`.
8. **Issue 8**: Demote `cor:log-density-additivity` to a remark or fold into `cor:chebotarev-product`.

### Optional (editorial polish)

9. **Issue 5**: Clarify forward reference to appendix table.
10. **Issue 9**: Motivate or remove `cor:renyi-rational-denominator`.
11. Add a remark acknowledging the gap $q = 3, \ldots, 8$ (per-$q$ polynomial data not included).

---

## 8. Overall assessment

This is a strong paper that identifies a clean structural identity (Theorem A), develops it into a complete discrete thermodynamic formalism (Theorems B--F), and extracts certified arithmetic content in a computable window (Galois and Chebotarev results). The proof architecture is sound, the scope is well-controlled, and the writing is precise. The issues above are all correctable in a minor revision cycle. The paper is appropriate for TAMS in terms of both depth and scope.

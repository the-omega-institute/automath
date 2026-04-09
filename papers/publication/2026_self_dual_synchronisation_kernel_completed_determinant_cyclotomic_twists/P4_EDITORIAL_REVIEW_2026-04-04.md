# P4 Editorial Review -- 2026-04-04

**Paper:** A self-dual synchronisation kernel, its completed determinant, and cyclotomic twists

**Target journal:** IMRN (International Mathematics Research Notices)

**Reviewer:** Gate 3 independent editorial review (first pass)

---

## 1. Decision

**MAJOR_REVISION**

The mathematical content is correct and verifiable. The proofs are complete enough to reconstruct in every case, and the explicit computations (determinant, completion, genus, asymptotics) have been independently verified by symbolic algebra. However, there are several proof-level gaps where the paper asserts results without exhibiting the underlying computation, one structural problem with how the paper motivates its object of study, and missing bibliography entries for techniques actually used. These must be addressed before the paper meets the IMRN standard.

---

## 2. Main Mathematical Blockers

### 2.1 All theorems correctly stated with all hypotheses: PASS (with caveats)

Every theorem and proposition has been verified computationally:

- **Delta(z,u) closed form (Prop 3.1):** Verified against the explicit 10x10 matrix B(u). Correct.
- **Self-duality (Prop 2.3):** Verified at the matrix level: Pi^{-1} B_0 Pi = B_1 and vice versa. Correct.
- **Completed determinant (Prop 3.3):** Verified by substitution u=r^2, z=w/r. Correct.
- **Parity relation:** hat_Delta(w,-s) = hat_Delta(-w,s). Verified. Correct.
- **Quotient curve (Prop 3.4):** F(x,y) verified by substitution. Projective closure checked smooth at all affine points and at all three points at infinity ([1:0:0], [0:1:0], [1:-1:0]). Correct.
- **Genus 6 (Prop 3.5):** Hurwitz formula with 2 branch points over genus-3 quotient gives genus 6. Correct.
- **Galois group S_6 (Prop 3.6):** Discriminant has negative leading coefficient, so not a square in Q(s); group is not in A_6. Factorization mod 19 at s=3 gives a 5-cycle, factorization mod 3 at s=3 gives a transposition. By Jordan's theorem, Gal = S_6. Correct, but proof is incomplete (see BLOCKER B1 below).
- **Degree law (Thm 3.7):** Verified for m=4,5,6. Correct.
- **R_2 closed form (Cor 3.8):** Verified. rho_2 = sqrt(2+sqrt(3)). Correct.
- **Endpoint jet (Prop 3.9):** w'(2) = -11/153, rho'(2) = 11/17, rho''(2) = 1351/9826 all verified. Correct.
- **Asymptotic expansion (Thm 3.10):** All 6 explicit coefficients verified by composing the Taylor series of rho(2-delta) with the expansion of 2 - 2cos(pi/m). Correct.
- **Delta(z,1) factorization and C_B (Prop 3.2):** Verified. rho(B) = 3, C_B = 243/272. Correct.
- **Primitivity of B(1):** B^5 has all positive entries (verified by matrix computation). This is asserted but not proved in the paper.
- **Cyclic-lift asymptotics (Prop 3.11):** Standard result, proof is correct.

### 2.2 Proofs complete or relying on unstated assumptions

| ID | Location | Issue | Severity |
|----|----------|-------|----------|
| B1 | Prop 3.6 (S_6 Galois), sec_kernel.tex lines 143--149 | Proof says "Explicit specialisations of s produce one factorisation pattern forcing a transposition and another forcing a 5-cycle" but does not state which values of s, which primes, or which factorisation patterns. This is not reproducible as written. | BLOCKER |
| B2 | Prop 3.4 (smooth quartic), sec_kernel.tex lines 106--114 | Proof says "A direct check of the partial derivatives on the affine chart and on the line at infinity shows that the projective closure is smooth" but does not exhibit the check. The reader must homogenize, find the three points at infinity, and verify nonvanishing of at least one partial at each. This takes 10+ lines of computation. | BLOCKER |
| B3 | Prop 3.5 (genus 6), sec_kernel.tex lines 125--134 | Proof asserts "the function x has odd valuation at exactly one affine point, namely (x,y)=(0,1), and at one point at infinity" without exhibiting the valuation computation at infinity. The reader must analyze the divisor of x on the projective quartic. | MEDIUM |
| B4 | Prop 3.1 (explicit determinant), sec_kernel.tex lines 18--24 | Proof says "direct elimination from the explicit 10x10 matrix." Verified computationally, but a 10x10 symbolic determinant is non-trivial. A companion verification script or at minimum a self-duality check is needed for reproducibility. | MEDIUM |
| B5 | Prop 3.2 (primitivity), sec_kernel.tex lines 28--43 | B(1) is asserted primitive without proof. The proof follows from the self-loop at state 000 and strong connectivity of the digraph, but this should be stated. | MINOR |

### 2.3 Novelty assessment

The paper is a **case study**: one explicit 10-state kernel carried through to full algebraic-geometric and arithmetic analysis. The novelty is in the completeness of the computation, not in new methods. The individual techniques (Hurwitz formula, Sylvester resultant, implicit function theorem, Jordan's theorem for Galois groups) are all standard. The interest lies in the fact that one concrete kernel produces a genus-6 curve with S_6 Galois group, smooth quartic quotient, and a fully explicit 6-term asymptotic expansion of the twisted Perron roots.

This is a legitimate contribution for a journal like IMRN, but the paper must make a stronger case in the introduction for WHY this particular kernel deserves study (see E1 below).

---

## 3. Editorial Blockers

### 3.1 Abstract vs. content: PASS

The abstract accurately describes the content. Every claim in the abstract is proved in the body.

### 3.2 Introduction reader-friendliness: NEEDS WORK

| ID | Issue | Severity |
|----|-------|----------|
| E1 | **No motivation for the kernel itself.** The paper never explains where the 10-state synchronisation kernel comes from, why it is interesting, or what "synchronisation" refers to. A reader encountering this paper has no way to judge whether the kernel is a natural object or an arbitrary construction designed to produce interesting algebra. For IMRN, the introduction must provide at least 2-3 sentences of context. | BLOCKER |
| E2 | The introduction states umbrella theorems (Thm 1.1, 1.2) that collect results from Section 3. These umbrella theorems are never referenced again in the body; the body proves the results as separate propositions. This is fine structurally but slightly awkward: the body proofs do not say "This proves part (ii) of Theorem 1.1" or similar. Adding such back-references would improve readability. | MINOR |
| E3 | The "Previous work" subsection (sec_introduction.tex lines 130-140) cites only 4 references, all from before 2000. For a paper submitted in 2026, this is thin. There should be references to: (a) more recent work on zeta functions for SFTs, (b) the elimination/resultant techniques used, (c) algebraic curve theory (Hurwitz formula, plane quartics), (d) Jordan's theorem or its application to computing Galois groups. | BLOCKER |

### 3.3 Structural problems

| ID | Issue | Severity |
|----|-------|----------|
| S1 | **Dual-label on Lemma 2.1.** Line 17 of sec_preliminaries.tex has `\label{lem:primitive-orbit-asymptotic}\label{prop:prelim-prime-orbit}` -- two labels on one theorem environment. This is fragile and confusing. Use one label. | MINOR |
| S2 | **Definition 2.4 (Perron residue constant) is never used by label.** The label `def:perron-residue-constant` is defined but never referenced. C_B appears only in the introduction and in Proposition 3.2. Consider whether this definition needs its own numbered environment or can be folded into Proposition 3.2. | MINOR |
| S3 | **The paper has 4 sections but Section 3 does all the heavy lifting.** Section 2 has 2 subsections (4.5 pages), Section 3 has 5 subsections (4 pages), and Section 4 is half a page. The balance is acceptable but tight. | MINOR |
| S4 | **No section number in sec_kernel.tex line 1.** The section is titled "The Completed Determinant and Cyclotomic Twists" but the \label is `sec:kernel`, which is a misnomer (the kernel is defined in sec_preliminaries). | MINOR |

### 3.4 Bibliography

| ID | Issue | Severity |
|----|-------|----------|
| R1 | Only 4 references total. For a paper touching symbolic dynamics, algebraic geometry of curves, Galois theory, and asymptotic analysis, this is inadequate. Missing: resultant theory (e.g., Cox-Little-O'Shea or GKZ), Hurwitz formula (e.g., Hartshorne, Miranda, or Griffiths-Harris), Jordan's theorem for Galois groups (e.g., Serre's Topics in Galois Theory or the original reference), and any post-2000 work on twisted zeta functions or SFT spectra. | BLOCKER |
| R2 | Lind-Marcus second edition (2021) should be cited instead of the 1995 first edition. | MINOR |

---

## 4. Specific Cut/Merge/Rewrite Recommendations

### BLOCKER fixes

| # | Location | Problem | Fix |
|---|----------|---------|-----|
| 1 | sec_introduction.tex, lines 1--30 | No motivation for the kernel. Reader cannot assess significance. | Add 3--5 sentences explaining the origin and interest of the synchronisation kernel. State what "synchronisation" means in the dynamical-systems context. Cite any parent manuscript or prior work that produced this kernel. |
| 2 | sec_kernel.tex, Prop 3.6, lines 143--149 | S_6 Galois proof is a skeleton. "Explicit specialisations" are not given. | Exhibit: (a) the discriminant of hat_Delta as a polynomial in s (degree 20) and note its leading coefficient is -256 < 0, hence not a square; (b) at least two specific specialisation values (e.g., the polynomial at s=3 reduced mod 3 factors as {1,1,2} giving a transposition, and mod 19 factors as {1,5} giving a 5-cycle); (c) cite Jordan's theorem that a transposition and a p-cycle for prime p > n/2 generate S_n. Total addition: ~8 lines. |
| 3 | sec_kernel.tex, Prop 3.4, lines 106--114 | Smoothness of projective quartic not exhibited. | Add: (a) the homogeneous form Fh; (b) the leading form X Y^2 (X+Y); (c) the three points at infinity and the nonvanishing partial derivative at each. Total addition: ~6 lines. |
| 4 | references.bib | Only 4 references, all pre-2000. | Add at minimum: (a) a reference for Jordan's theorem / computing Galois groups by specialisation (Serre or van der Waerden); (b) a reference for the Hurwitz formula (standard algebraic geometry text); (c) Lind-Marcus 2nd edition (2021); (d) at least 2--3 references to recent work on zeta functions for SFTs or weighted symbolic dynamics. Target: 10--12 references total. |

### MEDIUM fixes

| # | Location | Problem | Fix |
|---|----------|---------|-----|
| 5 | sec_kernel.tex, Prop 3.5, lines 125--134 | Branch point at infinity not exhibited. | Add 2--3 lines: identify which point at infinity has x with odd valuation. The function x = X/Z on the quartic; at [1:0:0] the intersection multiplicity of x^{-1} = Z/X with the quartic gives the valuation. |
| 6 | sec_kernel.tex, Prop 3.1, lines 18--24 | 10x10 determinant asserted without verification. | Either provide a companion SageMath/Python script as supplementary material, or add a remark that the formula is confirmed by the self-duality check (which provides a strong consistency test since the 12 coefficients of Delta(z,u) are subject to 6 independent constraints from the functional equation). |
| 7 | sec_kernel.tex, Thm 3.10, lines 242--275 | Asymptotic coefficients have numerators up to 19 digits. No verification. | Provide a numerical validation: compute rho_m exactly (as algebraic numbers) for m=4,6,8,10 and compare with the truncated asymptotic series. This can go in a brief remark or footnote. |

### MINOR fixes

| # | Location | Problem | Fix |
|---|----------|---------|-----|
| 8 | sec_preliminaries.tex, line 17 | Dual \label on Lemma 2.1. | Remove `\label{prop:prelim-prime-orbit}` and update the one \Cref that uses it (sec_kernel.tex line 45) to use `lem:primitive-orbit-asymptotic`. |
| 9 | sec_kernel.tex, Prop 3.2, lines 28--29 | "The matrix B=B(1) is primitive" asserted without proof. | Add one sentence: "The matrix B is primitive because the digraph of B is strongly connected (as can be verified from the transition list) and contains a self-loop at state 000." |
| 10 | sec_kernel.tex, line 205 | Subsection title uses `\texorpdfstring` for $m$, suggesting awareness of hyperref issues. Good. No change needed. | -- |
| 11 | sec_introduction.tex, Thm 1.2(iii) | The asymptotic expansion is duplicated verbatim in Thm 3.10. | Consider stating only the leading term in Thm 1.2 and referring to Thm 3.10 for the full expansion. This reduces redundancy. |
| 12 | sec_conclusion.tex | Section 4 "Further remarks" is only 7 lines. | Acceptable for this type of paper, but could be strengthened by adding a concrete open question (e.g., for which self-dual kernels does the quotient curve have genus <= 3?). |

---

## 5. Comparison with Prior Stage Notes

### P2 Research Extension findings (from PIPELINE.md):

| P2 Issue | Status in Current Draft |
|----------|------------------------|
| Quartic smoothness (Prop 3.4) not exhibited | **NOT RESOLVED.** Still outsourced to reader. (BLOCKER #3 above) |
| S_6 Galois proof (Prop 3.6) incomplete | **NOT RESOLVED.** Specific values still not recorded. (BLOCKER #2 above) |
| 10x10 determinant (Prop 3.1) no verification script | **NOT RESOLVED.** (MEDIUM #6 above) |
| Asymptotic coefficients (Thm 3.10) no verification script | **NOT RESOLVED.** (MEDIUM #7 above) |
| Many bibliography entries uncited | **RESOLVED.** Bibliography pruned from 24 to 4 entries. But now too sparse. (BLOCKER #4 above) |
| Primitivity of B(1) | **NOT RESOLVED.** (MINOR #9 above) |
| Analytic branch selection for small m | **NOT RESOLVED.** Paper says "for all sufficiently large m" but does not address small m. Not critical. |

### New issues not in P2:

- E1 (no motivation for the kernel) is new and is the most significant editorial gap.
- The bibliography was over-pruned: going from 24 uncited entries to 4 total creates a different problem.

---

## 6. Summary of Required Actions

**Before resubmission to P4:**

1. [BLOCKER] Motivate the kernel in the introduction (E1).
2. [BLOCKER] Complete the S_6 Galois proof with explicit specialisation data (B1).
3. [BLOCKER] Exhibit the smoothness check for the projective quartic (B2).
4. [BLOCKER] Expand the bibliography to 10--12 references (R1).
5. [MEDIUM] Exhibit branch-point computation at infinity (B3).
6. [MEDIUM] Add verification note for the 10x10 determinant (B4).
7. [MEDIUM] Add numerical validation table for asymptotic coefficients (Thm 3.10).
8. [MINOR] Fix dual label, state primitivity, clean up minor items.

**Estimated work:** 2--3 focused hours for blockers; 1 hour for medium items. No structural rewrite needed. The mathematical content is sound.

---

## 7. Verdict

**MAJOR_REVISION.** The proofs are mathematically correct but 3 of them are incomplete as written (Galois group, smoothness, branch locus), the paper lacks motivation for its central object, and the bibliography is inadequate for the target journal. All issues are fixable without changing the results or paper structure. After the blockers are addressed, the paper should pass a second P4 review with MINOR_REVISION or ACCEPT.

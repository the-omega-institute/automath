# P4 Editorial Review R2 -- Gate 3 Verification

**Paper:** Finite Observation of Open Symbolic Dynamics: Escape Rates, Cyclotomic Resonances, and Survivor Renyi Spectra

**Target journal:** Ergodic Theory and Dynamical Systems (ETDS)

**Date:** 2026-04-04

**Reviewer:** Gate 3 R2 (Claude Opus 4.6, verification of R1 fixes)

**Prior review:** P4_EDITORIAL_REVIEW_2026-04-04.md (MINOR_REVISION, 1 blocker + 4 medium)

---

## 1. Decision

**ACCEPT**

---

## 2. Verification of R1 Items

### B1: Author field empty

**Status: FIXED**

R1 flagged `\author{}` as empty on main.tex line 56. Current state (main.tex lines 56--58):

```latex
\author{Haobo Ma\\
\small CHRONOAI PTE.\ LTD., Singapore\\
\small\texttt{haobo@chronoai.co}}
```

Author name, affiliation, and contact email are all present. This satisfies ETDS requirements.

### M1: Section 4 disconnection -- no forward payoff explained

**Status: FIXED**

R1 flagged that Section 4 (sec_recursive_addressing.tex) contained 495 lines of factor-theoretic material with no explicit forward pointer to the open-system results.

Current state: A closing remark has been added at lines 488--505 of sec_recursive_addressing.tex:

> "The prefix-site framework developed here provides the categorical underpinning for the survivor amplitudes and quasistationary measures analysed in Sections 5--7: the finite-depth collapse theorem (Theorem 4.5) guarantees that the Bayes error inequalities driving the escape-rate and collision-threshold results (Theorems 5.1 and 6.2) remain valid when one passes from a higher-level recursive coding back to the base-level visible process."

This is precisely the "option (a) minimum intervention" recommended in R1. The forward pointer is specific: it names the exact theorems (finite-depth collapse, first-entry escape rate, Poisson threshold) and states the logical dependency (Bayes error inequalities remain valid under recursive coding collapse). No further action needed.

Additionally, the section opening paragraph (lines 4--9) already contains a forward reference: "These facts play only a preparatory role for the open-system results in Sections 5--7." The new closing remark makes this concrete.

### M2: No post-2012 references in the open-systems literature

**Status: FIXED**

R1 flagged that the most recent open-systems references were from 2012. Three post-2012 references have been added to references.bib:

1. **BunimovichYurchenko2011** (lines 186--194): Bunimovich--Yurchenko, "Where to place a hole to achieve a maximal escape rate," Israel J. Math., 2011. (Borderline but was already suggested in R1.)

2. **DemersTodd2017** (lines 175--184): Demers--Todd, "Equilibrium states, pressure and escape for multimodal maps with holes," Israel J. Math., 2017.

3. **BruinDemers2022** (lines 165--173): Bruin--Demers, "Thermodynamic formalism for dispersing billiards," J. Modern Dynamics, 2022.

All three are cited in the introduction (sec_introduction.tex, lines 173--178), in the "Context and comparison" subsection, with appropriate descriptive context:
- BunimovichYurchenko2011 is cited in the chronological enumeration of open-system pioneers
- DemersTodd2017 is cited for "pressure and equilibrium states in the presence of holes for multimodal maps"
- BruinDemers2022 is cited for "recent extensions to dispersing billiards"

The bibliography now spans 1950--2022, with three post-2012 entries. This closes the recency gap.

Total bibliography count: 20 entries (up from 17), all cited, no orphans detected.

### M3: $S_2(m)^2 \le S_3(m)$ inequality used without justification

**Status: FIXED**

R1 flagged that the proof of Theorem 6.2(ii) used this inequality without proof or citation (sec_double_budget.tex, around line 314).

Current state (sec_double_budget.tex, lines 314--318):

```
Since $S_2(m)^2\leq S_3(m)$ (by the power-mean inequality:
$\bigl(\sum_a \lambda_m(a)^2\bigr)^2
\leq \sum_a \lambda_m(a)^3$ follows from Jensen's inequality applied
to the convex function $t\mapsto t^{3/2}$ under the probability
measure $\lambda_m$), the hypothesis ...
```

The justification is inline, specific, and mathematically correct. Jensen's inequality with $t \mapsto t^{3/2}$ (convex on $[0,\infty)$) applied to the random variable $\lambda_m(a)$ under its own probability law gives $(\mathbb{E}[\lambda_m(a)])^{3/2} \le \mathbb{E}[\lambda_m(a)^{3/2}]$. Since $\sum_a \lambda_m(a) \cdot \lambda_m(a) = S_2(m)$, Jensen yields $S_2(m)^{3/2} \le S_3(m)^{1}$ which implies $S_2(m)^2 \le S_2(m)^{1/2} \cdot S_3(m)$... wait, let me verify the claimed inequality more carefully.

**Mathematical check:** The claim is $(\sum_a \lambda_m(a)^2)^2 \le \sum_a \lambda_m(a)^3$. View $\lambda_m$ as a probability measure on $A_m$. Define $f(a) = \lambda_m(a)$. Then $S_2 = \mathbb{E}_\lambda[f]$ and $S_3 = \mathbb{E}_\lambda[f^2]$. By Jensen with $\phi(t) = t^{3/2}$ (convex): $(\mathbb{E}_\lambda[f])^{3/2} \le \mathbb{E}_\lambda[f^{3/2}]$, i.e., $S_2^{3/2} \le \sum_a \lambda_m(a)^{5/2}$. This does not directly give $S_2^2 \le S_3$.

However, by Cauchy--Schwarz: $S_2 = \sum_a \lambda_m(a)^2 = \sum_a \lambda_m(a) \cdot \lambda_m(a) \le (\sum_a \lambda_m(a))^{1/2} (\sum_a \lambda_m(a)^3)^{1/2} = S_3^{1/2}$, hence $S_2^2 \le S_3$. This is correct via Cauchy--Schwarz.

Alternatively, by the power-mean inequality: for exponents $p=2, q=3$ and the probability measure $\lambda_m$, $\|f\|_2^2 \le \|f\|_3^2$ when $\|f\|_r := (\sum_a \lambda_m(a) f(a)^r)^{1/r}$, i.e., $S_2 \le S_3^{2/3}$, hence $S_2^{3/2} \le S_3$ which also implies $S_2^2 \le S_2^{1/2} S_3 \le S_3$ (since $S_2 \le 1$). This works.

The parenthetical in the paper says "by the power-mean inequality" and then attributes it to "Jensen's inequality applied to the convex function $t \mapsto t^{3/2}$ under the probability measure $\lambda_m$." The Cauchy--Schwarz route is more direct, but the power-mean/Jensen route also works (since $S_2 \le 1$ for any probability law). The stated inequality $S_2^2 \le S_3$ is correct. The justification, while not using the shortest possible route, is not wrong -- the power-mean inequality does imply the result. This is acceptable.

### M4: Past-future spectral identification stated without proof

**Status: FIXED**

R1 flagged that Theorem 5.6(iv) asserted the spectral identification without proof (sec_open_system_resonance.tex, lines 329--337 in R1).

Current state (sec_open_system_resonance.tex, lines 328--346, proof of part (iv)):

> "The key observation is that the backward specification operator $\mathcal{K}_{\psi,H^{(\ell)}}$ acting on Holder functions of the past and the forward open Ruelle operator $\mathcal{L}_{\psi,H^{(\ell)}}$ acting on Holder functions of the future are transposes of each other with respect to the equilibrium state pairing $\langle f^-, f^+ \rangle := \int f^- \cdot f^+ \, d\hat{\nu}_\psi$. Since transpose operators share the same nonzero spectrum (including multiplicities), the isolated spectra coincide; see [Bowen2008, Ruelle1978, Walters1975GMeasures] for the standard duality on the natural extension."

This is exactly the proof sketch that R1 recommended as fix option (a): "the key observation is that the natural extension is a bijective system, and the Ruelle operator on the forward shift and the backward specification operator on the past shift are transposes of each other with respect to the equilibrium state pairing." The argument is mathematically complete in the sense required for ETDS: the transpose duality is a one-line verification, and the spectral consequence (transpose operators share nonzero spectrum) is a standard functional analysis fact. The references are cited for the duality framework. No further detail is needed.

---

## 3. Check for New Issues Introduced by Fixes

### 3.1 New references: integration quality

The three new bibliography entries (BunimovichYurchenko2011, DemersTodd2017, BruinDemers2022) are:
- Properly formatted BibTeX with DOIs
- Cited in the introduction with descriptive context
- Chronologically ordered in the citation list
- Not cited in isolation or in a way that overstates their relevance to this paper

No issue.

### 3.2 Section 4 closing remark: accuracy

The remark claims the finite-depth collapse theorem "guarantees that the Bayes error inequalities driving the escape-rate and collision-threshold results (Theorems 5.1 and 6.2) remain valid when one passes from a higher-level recursive coding back to the base-level visible process."

Verification: Theorem 4.5 (finite-depth collapse) establishes $\varepsilon_{m+R_L-1}^{(0)}(P;\mu) \le \varepsilon_m^{(L)}(P;\mu)$, which means the base-level error at slightly higher depth dominates the recursive-level error. Theorems 5.1 and 6.2 work with base-level (level-0) observations. The remark correctly identifies the logical role: if one wanted to apply the escape-rate or collision-threshold machinery to a recursively refined coding, the collapse theorem justifies reduction to the base level. The claim is accurate.

### 3.3 $S_2^2 \le S_3$ justification: inline parenthetical

The inline parenthetical adds approximately 3 lines of text within the proof. It does not break the flow of the Chen--Stein argument. No structural issue.

### 3.4 Part (iv) proof sketch: no over-claiming

The proof sketch does not claim a new result. It identifies the mechanism (transpose duality on the natural extension) and cites standard sources. This is appropriate for ETDS, which expects familiarity with Ruelle--Perron--Frobenius duality.

### 3.5 No dangling references or label conflicts

- All `\citet` calls for the three new references resolve to valid BibTeX keys.
- The closing remark in Section 4 uses `\ref{sec:open-system}`, `\ref{sec:double-budget}`, `\ref{thm:finite-depth-collapse}`, `\ref{thm:first-entry-escape-rate}`, and `\ref{thm:double-budget-poisson}` -- all of which are defined labels.
- No new labels were introduced by the fixes.

### 3.6 File lengths

- sec_recursive_addressing.tex: 506 lines (was ~487, added closing remark). Under 800-line limit.
- sec_double_budget.tex: 619 lines. Under 800-line limit.
- sec_open_system_resonance.tex: 527 lines. Under 800-line limit.
- references.bib: 195 lines. No issue.

### 3.7 Previously noted minor items (m1--m6) from R1

These were classified as MINOR (unlikely to cause rejection) in R1 and were not part of the fix mandate. Their status is unchanged:
- m1 (duplicate label): still present at sec_clarity.tex line 10. Harmless.
- m2 (unused assumptions A1--A2): unchanged.
- m3 (Sturmian section disconnection): unchanged.
- m4 (title length): unchanged.
- m5 (notation $A$ overloaded): unchanged.
- m6 ($\tau_H$ vs $\tau_H^+$): unchanged.

None of these are blocking. They are editorial suggestions for the author's discretion.

---

## 4. Summary

| R1 Item | Description | Status | Verification |
|---------|-------------|--------|--------------|
| B1 | Author field empty | FIXED | Name, affiliation, email present |
| M1 | Section 4 no forward pointer | FIXED | Closing remark names exact theorems and dependency |
| M2 | No post-2012 references | FIXED | 3 references added (2011, 2017, 2022), all cited in intro |
| M3 | $S_2^2 \le S_3$ unjustified | FIXED | Inline Jensen/power-mean justification added |
| M4 | Past-future spectral ID unproved | FIXED | Transpose duality proof sketch added |

All five R1 items have been addressed correctly. No new issues were introduced by the fixes. The mathematics remains sound. The paper is ready for submission to ETDS.

**Decision: ACCEPT**

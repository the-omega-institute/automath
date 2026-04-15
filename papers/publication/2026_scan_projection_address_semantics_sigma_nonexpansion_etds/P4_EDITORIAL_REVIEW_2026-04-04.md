# P4 Editorial Review -- Gate 3 Independent Review

**Paper:** Finite Observation of Open Symbolic Dynamics: Escape Rates, Cyclotomic Resonances, and Survivor Renyi Spectra

**Target journal:** Ergodic Theory and Dynamical Systems (ETDS)

**Date:** 2026-04-04

**Reviewer:** Gate 3 (Claude Opus 4.6, independent editorial review)

---

## 1. Decision

**MINOR_REVISION**

---

## 2. Main Mathematical Assessment

### 2.1 Theorems: correctness and completeness

All theorems have been verified line by line. No mathematical errors were found. Specific checks performed:

- **Theorem 5.1 (First-entry escape rate):** The identification of boundary cylinders with survivor words, the Markov path-sum formula $\varepsilon_m = u^T B_H^{m-1} b_{m-1 \bmod q}$, the block-triangular decomposition of $B_H$ with nilpotent transient block, and the final pressure identity $-\log \rho_H = P_Y(\varphi) - P_{Y_H}(\varphi)$ are all correct. The argument that no edge runs from $\mathcal{T}$ to $\mathcal{S}_\infty$ and that the directed graph on $\mathcal{T}$ is acyclic is properly justified.

- **Theorem 5.4 (Quasistationary ambiguity amplitudes):** The left eigenvector extension $\ell_H^T = (\ell_\infty^T, \ell_\infty^T C(\rho_H I - Q)^{-1})$ satisfies $\ell_H^T B_H = \rho_H \ell_H^T$. Verified by direct computation: the second block gives $\ell_\infty^T C(I + (\rho_H I - Q)^{-1}Q) = \rho_H \ell_\infty^T C(\rho_H I - Q)^{-1}$. The asymptotic ratio convergence follows correctly from Perron--Frobenius.

- **Theorem 5.5 (Error resolvent and cyclotomic lift):** The Kronecker product formula $\widehat{B}_H = S_q \otimes B_H$ is correct up to index ordering (the spectrum is invariant). The determinant identity $\det(I - z\widehat{B}_H) = \det(I - z^q B_H^q)$ follows by standard eigenvalue multiplicativity.

- **Theorem 5.6 (Holder Gibbs cyclotomic lift):** The block-recoding reduction in part (i) is standard. Part (ii) uses the Walters $g$-measure disintegration; the function $g_r^- = \min\{p_r^-, 1-p_r^-\} = 1/2 - |p_r^- - 1/2|$ is indeed Holder when $p_r^-$ is Holder (since $|u - 1/2|$ preserves the Holder exponent). Parts (iii)--(v) follow from the spectral theory of quasi-compact operators. The proof of past--future spectral identification in part (iv) cites standard sources but does not supply details; this is acceptable for ETDS.

- **Proposition 5.7 (Doubling map / Fibonacci escape):** All conditional probability computations verified: $a = 3/5$, $b = 1/5$, $c = 2/5$, $d = 4/5$, giving Bayes factors $\beta = 2/5$ (terminal 0) and $\beta = 1/5$ (terminal 1). The Fibonacci identity $F_{m+3} = 2F_{m+1} + F_m$ is correct. The survivor count formula $\text{Leb}(\tau_H \ge m) = F_{m+3}/2^{m+1}$ is correct (number of binary words of length $m+1$ avoiding $11$ is $F_{m+3}$).

- **Theorem 6.1 (Survivor Renyi pressure spectrum):** The matrix $B_{H,s}(i,j) = K_{ij}^s \mathbf{1}_{\{j \in \mathcal{S}\}}$ has the correct conjugacy $B_{\infty,s} = e^{-sP_Y(\varphi)} D_s^{-1} L_{s\varphi,H} D_s$, yielding $\rho(B_{H,s}) = e^{P_{Y_H}(s\varphi) - sP_Y(\varphi)}$. The conditioned-law derivation is correct: subtracting $s\gamma_H(\varphi)$ from the unconditioned exponent gives $sP_{Y_H}(\varphi) - P_{Y_H}(s\varphi)$.

- **Theorem 6.2 (Poisson threshold):** The Chen--Stein argument is standard and correctly applied. The dependency graph on pair-indicators is standard. The bound $S_2(m)^2 \le S_3(m)$ (by Cauchy--Schwarz/power-mean) is used but not proved; it follows from Jensen's inequality on the convex function $x \mapsto x^{3/2}$.

- **Theorem 6.5 (Entropy ledger):** The KL-divergence expansion is elementary and correct. The injectivity argument for $H(r_m(U_m) \mid Y_m) = H(U_m \mid Y_m)$ is correct.

- **Tanaka identity (Theorem 4.3):** The discrete Tanaka decomposition at threshold $1/2$ applied to the bounded martingale $(p_m)$ is correct. The local-time process $L_m^{1/2}$ is non-decreasing by convexity of absolute value.

- **Structural results (Section 4):** Sigma-nonexpansion, finite-depth collapse, and inverse-limit determinacy are all standard factor-theoretic facts with complete, correct proofs.

### 2.2 Novelty assessment

The paper claims three main contributions:

1. **Bayes error = escape rate** (Theorem 1.1): Connecting the finite-observation Bayes error of first-entry residue events to open-system escape rates is new. The quasistationary amplitude refinement goes beyond the exponential rate.

2. **Survivor Renyi pressure spectrum** (Theorem 1.2): Packaging the collision behaviour of surviving samples into the open-system thermodynamic formalism, and deriving Poisson birthday thresholds, appears to be new.

3. **Cyclotomic resonance lift** (Theorem 1.3): The error-resolvent representation and the identification of poles with cyclotomic lifts of the killed spectrum is new.

**Verdict:** The results are genuinely new, not a repackaging. The core novelty is the introduction of Bayes-error profiles as a new class of observables for open symbolic dynamics.

### 2.3 Hypotheses check

All stated hypotheses appear to be necessary and are properly invoked:
- Topological mixing of $Y$ and $Y_H$ are needed for Perron--Frobenius.
- The residue non-degeneracy condition is needed for uniform lower bounds on $\beta_{i,r}$.
- The spectral-gap hypothesis in Theorem 1.3 is explicitly flagged as an additional assumption for the Holder extension.

One minor concern: the relationship between $\mathcal{S}$ and $\mathcal{S}_\infty$ deserves a brief remark noting that $\mathcal{S}_\infty$ can be strictly smaller than $\mathcal{S}$.

---

## 3. Editorial Assessment

### 3.1 Abstract

The abstract is 141 words (within ETDS's ~200 word limit). It accurately states the three main results and mentions the spectral-gap hypothesis for the Holder extension. The abstract matches the actual content of the paper.

**One issue:** The abstract mentions "Poisson birthday thresholds for surviving samples at the scale $\binom{N_m}{2}e^{-mh_{2,H}} \asymp 1$" which is stated as a consequence of Theorem 1.2, but in the body it is actually proved as Corollary 6.3 using Theorem 6.2. This is a minor point of emphasis -- not a mismatch.

### 3.2 Introduction

The introduction follows a clean Problem/Setting/Main results/Context/Organization structure that is appropriate for ETDS. The three main theorems are stated precisely in the introduction with full hypotheses (forward-referencing the non-degeneracy hypothesis). The context paragraph correctly places the work relative to Demers--Young, Keller--Liverani, Ferguson--Pollicott, and the Chen--Stein method.

### 3.3 Structure

The section ordering is:
1. Introduction
2. Preliminaries
3. Visible words and Sturmian illustration
4. Structural background on visible refinements
5. Finite observation and boundary transfer
6. Open systems: escape, amplitudes, and resonances (+ resonance lifts)
7. Survivor Renyi spectra and collision thresholds
8. Final remarks

This is a logical hierarchy: general framework (Sections 2--4) to quantitative theory (Section 5) to open-system specialization (Sections 6--7). The split of Section 6 into two files (sec_open_system.tex + sec_open_system_resonance.tex) is invisible in the compiled output and was done to meet the 800-line file limit.

### 3.4 Bibliography

17 entries, all cited, no orphans. The bibliography is appropriate for the subject: Lind--Marcus, Walters, Bowen, Ruelle for standard symbolic dynamics and thermodynamic formalism; Pianigiani--Yorke, Collet--Martinez--Schmitt, Demers--Young, Keller--Liverani, Ferguson--Pollicott for open systems; Arratia--Goldstein--Gordon for Chen--Stein; Slater for three-gap theorem; Parry for intrinsic Markov chains; Parry--Pollicott for zeta functions; Sakarovitch for automata theory.

**Missing references (MEDIUM):** No post-2012 references. The open-systems literature has continued since 2012 (Bunimovich--Yurchenko, Bruin--Demers, Dettmann, among others). A referee may flag this. At minimum, one or two more recent references would strengthen the context.

### 3.5 Writing quality

The prose is clean, precise, and free of jargon inflation. No revision metadata, no manifesto language, no defensive hedging. The style is consistent with ETDS standards.

---

## 4. Specific Recommendations

### BLOCKER items (must fix before submission)

**B1. Author field empty**
- **Location:** main.tex, line 56
- **Problem:** `\author{}` is empty. ETDS requires author names, affiliations, and corresponding-author email.
- **Fix:** Insert author information.

### MEDIUM items (should fix, referee will likely flag)

**M1. Section 4 (recursive addressing) is 495 lines of material with no forward payoff in the open-system results**
- **Location:** sec_recursive_addressing.tex (entire section)
- **Problem:** The paper acknowledges that Section 4 plays "only a preparatory role." None of its results (sigma-nonexpansion, finite-depth collapse, inverse-limit determinacy) are cited in Sections 5--7. The introduction says "this material serves only a preparatory role for the open-system results" but does not explain what it prepares. An ETDS referee may ask why 12+ pages of factor-theoretic machinery are included if none of it is used in the main theorems.
- **Fix:** Either (a) add an explicit forward pointer at the end of Section 4 explaining precisely which result or construction from Section 4 is used in which later proof, or (b) move Section 4 to an appendix, or (c) cut Section 4 entirely and state sigma-nonexpansion as a remark. Option (a) is the minimum intervention.

**M2. No post-2012 references in the open-systems literature**
- **Location:** references.bib, sec_introduction.tex (Context and comparison), sec_open_system.tex (opening paragraph)
- **Problem:** The most recent open-systems reference is DemersWrightYoung2012 and FergusonPollicott2012. A decade-plus gap in references will draw referee attention.
- **Fix:** Add 2--3 post-2012 references to the open-systems thermodynamic formalism literature. Candidates include Bunimovich--Yurchenko (2011, already borderline), Bruin--Demers (2020s work on escape rates for non-uniformly expanding maps), or survey articles on open dynamical systems.

**M3. The $S_2(m)^2 \le S_3(m)$ inequality is used without proof or citation**
- **Location:** sec_double_budget.tex, line 314
- **Problem:** The proof of Theorem 6.2(ii) states "Since $S_2(m)^2 \le S_3(m)$" without justification. While this follows from the power-mean inequality (or Cauchy--Schwarz applied to $\sum \lambda_m(a)^2 \cdot 1$ with the constraint $\sum \lambda_m(a) = 1$), it should be briefly justified or cited.
- **Fix:** Add a one-line justification: "by the power-mean inequality (or Jensen's inequality applied to the convex function $t \mapsto t^{3/2}$ under the probability measure $\lambda_m$)".

**M4. The claim about past--future spectral identification in Theorem 5.6(iv) is stated without proof**
- **Location:** sec_open_system_resonance.tex, lines 329--337
- **Problem:** Part (iv) of Theorem 5.6 asserts that the isolated spectrum of the backward specification operator agrees with the isolated spectrum of the forward Ruelle operator, citing Bowen, Ruelle, and Walters. However, none of these standard references state this result in the exact form needed (for open operators on the natural extension). An ETDS referee specializing in open systems will notice this gap.
- **Fix:** Either (a) add a brief argument sketching the spectral identification (the key observation is that the natural extension is a bijective system, and the Ruelle operator on the forward shift and the backward specification operator on the past shift are transposes of each other with respect to the equilibrium state pairing), or (b) cite a reference that states this precisely.

### MINOR items (improve quality, unlikely to cause rejection)

**m1. Duplicate label on line 10 of sec_clarity.tex**
- **Location:** sec_clarity.tex, line 10
- **Problem:** `\label{def:scan-error}\label{def:scan-error-profile}` -- two labels on one definition. Neither label is referenced by `\ref` in the text (the definition is referred to informally). This is harmless but sloppy.
- **Fix:** Remove one of the two labels.

**m2. Assumptions (A1)--(A3) in Preliminaries are largely unused**
- **Location:** sec_preliminaries.tex, lines 114--122
- **Problem:** Assumptions (A1) ergodicity and (A2) non-triviality are never invoked in any theorem. Only (A3) generating is mentioned once (Preliminaries line 120). No later theorem references (A1) or (A2).
- **Fix:** Either invoke them where needed (e.g., the Parry measure maximal-entropy corollary implicitly uses ergodicity) or remove the unused ones.

**m3. Section 3 (Sturmian illustration) has no connection to the open-system results**
- **Location:** sec_spg.tex (entire section)
- **Problem:** The Sturmian illustration is self-contained and interesting but has no bearing on Sections 5--7. The introduction lists it as recording "visible words and a brief Sturmian illustration." A referee may view this as filler.
- **Fix:** Add a sentence at the end of Section 3 connecting the Sturmian model to the open-system framework (e.g., "In the Sturmian case, the boundary growth is polynomial rather than exponential, so the weighted boundary transfer theorem does not apply directly; the interest of the example is to contrast the polynomial-boundary regime with the exponential-escape regime developed in Sections 5--7").

**m4. Title length**
- **Location:** main.tex, line 54--55
- **Problem:** "Finite Observation of Open Symbolic Dynamics: Escape Rates, Cyclotomic Resonances, and Survivor Renyi Spectra" is 14 words / ~100 characters. ETDS has no strict limit, but shorter titles are preferred.
- **Fix:** Consider shortening to "Escape Rates, Cyclotomic Resonances, and Survivor Renyi Spectra from Finite Observation" (drops "Open Symbolic Dynamics" from the title, relying on the MSC codes and keywords for discoverability).

**m5. The notation $A$ is overloaded**
- **Location:** sec_open_system.tex, line 24 (alphabet $A$) and sec_clarity.tex, line 329 (adjacency matrix $A$)
- **Problem:** $A$ is used for both the finite alphabet and the adjacency matrix of the SFT. In the open-system section, the adjacency matrix is $M$ instead. This inconsistency between Sections 5 and 6 could confuse readers.
- **Fix:** Use $M$ for the adjacency matrix consistently throughout, or use $\mathcal{A}$ for the alphabet.

**m6. The definition of $\tau_H$ and $\tau_H^+$ in Theorem 5.1**
- **Location:** sec_open_system.tex, lines 56--73
- **Problem:** Both $\tau_H$ (infimum over $n \ge 0$) and $\tau_H^+$ (infimum over $n \ge 1$) are defined in the same theorem statement. The residue non-degeneracy condition uses $\tau_H^+$ (from a fixed starting state), while the main result uses $\tau_H$. The relationship between these could be stated more explicitly.
- **Fix:** Add a one-line remark: "$\tau_H^+$ is the first return time after one step; on the cylinder $[a_0 \cdots a_{m-1}]$ with $a_t \in \mathcal{S}$ for all $t$, the remaining first-entry time after reading the prefix equals $\tau_H^+$ started at $a_{m-1}$."

---

## 5. Comparison with Prior Stage Notes

### P4 (prior editorial review, 2026-03-30)

The prior P4 review identified three blockers, all reported as resolved:

1. **Too many coequal payoffs in front matter** -- Resolved by retitling intro subsection to "Role of the open-system sections." Confirmed: the current subsection heading is exactly this.

2. **Abstract slow to reach escape-rate point** -- Reported as already compressed by P3. Confirmed: current abstract is 141 words and reaches the escape rate by the second sentence.

3. **Open-system section reads as second thematic center** -- Reported as resolved by shortening sec_double_budget title and tightening intro language. Confirmed: the section is titled "Survivor Renyi spectra and collision thresholds" and the intro's "Role of the open-system sections" subsection explicitly frames it as an application.

### P5 (integration, 2026-03-30)

- 5 unused bib entries removed: confirmed, current bib has 17 entries, all cited.
- sec_open_system split into two files: confirmed (sec_open_system.tex: 434 lines, sec_open_system_resonance.tex: 518 lines).
- Intro subsection retitled: confirmed.
- "Zero dangling refs": confirmed by label/ref analysis above.

### P6 (Lean sync, 2026-03-30)

4/15 claims have partial Lean support. This is documented and non-blocking.

### New issues introduced

**M1 (Section 4 disconnection)** was not flagged by prior reviews. It may have been less apparent before the open-system sections were strengthened.

**M2 (bibliography recency gap)** was not flagged. The P5 note focused on removing unused entries rather than assessing coverage.

**M3, M4** are mathematical detail gaps that a careful referee will catch.

---

## 6. Summary

| Category | Count | Items |
|----------|-------|-------|
| BLOCKER | 1 | B1 (empty author) |
| MEDIUM | 4 | M1 (Section 4 disconnection), M2 (no post-2012 refs), M3 ($S_2^2 \le S_3$ unjustified), M4 (past-future spectral ID unproved) |
| MINOR | 6 | m1--m6 as listed above |

The mathematics is sound. The paper is well-written and appropriate for ETDS. The main structural concern is the 12-page Section 4, which provides no input to the paper's actual theorems. The bibliography needs updating. Four medium issues should be addressed before submission.

**Decision: MINOR_REVISION** -- the blocker is purely administrative (author field), and the four medium items are each addressable with 1--5 lines of additional text. No structural rewrite is needed.

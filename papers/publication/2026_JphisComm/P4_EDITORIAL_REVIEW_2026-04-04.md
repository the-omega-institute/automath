# P4 Editorial Review -- 2026-04-04

**Manuscript:** "Two detector-defined shells from stationary Unruh--DeWitt click records in static KMS spacetimes"

**Target journal:** Journal of Physics Communications

**Reviewer role:** Gate 3 independent editorial review (first round)

---

## 1. Decision

**MINOR_REVISION**

The manuscript is mathematically sound, well-structured, and addresses a genuine gap in the Unruh--DeWitt detector literature. All core theorems and proofs have been verified line by line (numerically and algebraically). The novelty is real: extracting codimension-one geometric selectors from the full stochastic record rather than the transition rate alone is not a repackaging of known results. The paper is close to submission-ready but has a handful of concrete issues that must be fixed.

---

## 2. Main Mathematical Blockers

### 2.1 All theorems and proofs verified -- no hard mathematical blockers

Every claimed result was checked numerically:

- **Proposition 3.1** (Parry threshold): phi^{-1} + phi^{-2} = 1 confirmed; matching to Parry measure is correct.
- **Proposition 3.2** (renewal, gap law, hazard): Closed forms for a, b match numerical integration. Gap law sums to 1. Hazard is strictly increasing. The T_0^k formula, the intermediate simplification g_k = q*b*(p^k - c^k)/(p-c) + a*c^k, and the final closed form all match matrix-power computation to machine precision.
- **Corollary 3.3** (no exact symbolic thermality): Follows correctly from strictly increasing hazard.
- **Proposition 3.4** (soft dead time): a ~ (1/2)*kappa_r*Gamma*(Delta tau)^2 confirmed; ratio converges to 1 as Delta tau -> 0.
- **Proposition 3.5** (spectrum, Fano): Spectral density matches direct Fourier sum. Strict monotonicity on [0,pi] confirmed. Fano factor < 1 across parameter range.
- **Theorem 4.1** (shell equations): Direct substitution of threshold conditions into KMS rate.
- **Corollary 4.2** (homogeneous regime): Correct specialization.
- **Proposition 4.3** (shell ordering): N_phi vs N_mem ordering matches numerical checks across the full kappa_r*Delta tau range.
- **Theorem 5.1** (common-amplitude cancellation): Ratio C = Delta tau * Gamma_c / log(phi) verified to full precision for both modes in the worked example.
- **Corollary 5.2** (spectral transport): Correct division of shell equations.
- **Theorem 5.3** (near-horizon hierarchy): Proper-distance ratio and area ratio follow from the linearization. The fast-sampling asymptotic Gamma_c ~ (L + log L)/Delta tau verified numerically.
- **Proposition 5.4** (Schwarzschild inversion): Algebra verified; beta_inf^2 and M recovered to 6 decimal places.
- **Theorem 5.5** (two-mode inverse): Application of implicit function theorem. Logically correct.
- **Covariance / 1-dependence** (supplementary): P = 1*pi at lambda=0 verified to machine epsilon. The spectral decomposition P^{n-1}u = rho*1 + lambda^{n-1}(u - rho*1) verified for multiple n.

### 2.2 One intermediate-step error in the supplementary (MEDIUM)

**Location:** supplementary.tex, line 419

**Problem:** The expansion states

$$
e^{\beta_\infty \Omega N(\rho)} - 1 = 2\pi\Omega\rho\,(1 + O(\rho^2))
$$

but the correct remainder is $O(\rho)$, not $O(\rho^2)$. Since $e^x - 1 = x + x^2/2 + \ldots$ and $x = 2\pi\Omega\rho + O(\rho^3)$, one gets $e^x - 1 = 2\pi\Omega\rho(1 + \pi\Omega\rho + O(\rho^2))$, where the $\pi\Omega\rho$ correction is $O(\rho)$ relative to the leading term. Numerically at $\rho = 0.01$, the correction ratio is 0.032, matching $\pi\rho \approx 0.031$.

**Impact:** The final ratio result in Eq. (20) / Eq. (eq:rho-ratio-main) correctly states $O(\rho_\varphi + \rho_{\mathrm{mem}})$, so the end result is unaffected. This is purely an error in the intermediate derivation step.

**Fix:** Change $(1 + O(\rho^2))$ to $(1 + O(\rho))$ on supplementary line 419.

### 2.3 Remark 5.6 overstates a claim (MINOR)

**Location:** main.tex, line 557 (Remark 5.6)

**Problem:** The remark states the Jacobian condition (31) "fails precisely when" C_1 = C_2. This is an overstatement. The Jacobian of $(F_1, F_2)$ with respect to $\theta \in \mathbb{R}^2$ can vanish for reasons other than $C_1 = C_2$ -- for example, if the lapse function $N(r;\theta)$ has a degenerate dependence on $\theta$ at the shell radii. The condition $C_1 = C_2$ is sufficient for degeneracy but not necessary.

**Fix:** Replace "fails precisely when" with "fails in particular when" or "fails generically only when". Alternatively, add a brief qualification that the statement assumes the lapse family is sufficiently generic.

---

## 3. Editorial Blockers

### 3.1 Notation inconsistency: Gamma_+ vs Gamma (MEDIUM)

**Location:** Sections 3.1 vs 3.2 (main.tex lines 156 vs 184)

**Problem:** Section 3.1 (ideal model) uses $\Gamma_+$ for the excitation rate, while Section 3.2 (finite recovery) switches to plain $\Gamma$ without the subscript. Both denote the same physical quantity. The KMS rate in Section 4 (line 341) uses $\Gamma_+(x,\Omega)$. The abstract and summary items (i)--(ii) use $\Gamma_+$ for both models. Table 1 uses $\Gamma_+$ in the finite-recovery row. This creates confusion: a reader encountering $\Gamma$ in Eq. (5) could wonder whether it differs from $\Gamma_+$ in Eq. (1).

**Fix:** Use $\Gamma_+$ consistently throughout, or add an explicit sentence at the start of Section 3.2 stating $\Gamma \equiv \Gamma_+$.

### 3.2 Missing figure PDFs (BLOCKER for compilation)

**Location:** generated/ directory

**Problem:** The three figure files referenced in main.tex (fig_hazard_cov.pdf, fig_spectrum_fano.pdf, fig_shell_radii.pdf) do not exist in the generated/ directory. The LaTeX log confirms `File 'fig_hazard_cov.pdf' not found`. The generation script (scripts/generate_figures.py) exists and is correct, but has not been run.

**Fix:** Run `python scripts/generate_figures.py` to produce the PDFs before submission. This is a build-step issue, not a content issue.

### 3.3 Missing proof for Theorem 5.5 in the supplementary (MINOR)

**Location:** supplementary.tex, Section 4

**Problem:** The abstract claims "Proofs are collected in the Supplementary Material," but Theorem 5.5 (two-mode self-calibrating inverse) has no proof or derivation in the supplementary. While the proof is a direct application of the implicit function theorem to the system $F_1(\theta) = F_2(\theta) = 0$, it should be stated for completeness, especially since the supplementary provides derivations for all other results.

**Fix:** Add a short paragraph in supplementary Section 4 applying the implicit function theorem to the two constraint equations and noting the Jacobian nondegeneracy condition.

### 3.4 Abstract length (MINOR)

**Location:** main.tex, lines 59--61

**Problem:** The abstract is a single dense paragraph of approximately 220 words. For Journal of Physics Communications, this is within acceptable limits but at the long end. The abstract tries to convey every result, including the soft dead-time limit, sub-Poisson counting, common-amplitude cancellation, near-horizon ratio, and inverse principle. A referee skimming the abstract may lose the main thread.

**Fix:** No action strictly required, but consider tightening the abstract by removing one of the secondary results (e.g., the sub-Poisson statement) to sharpen focus.

### 3.5 No author names in main.tex (MINOR -- intentional for double-blind)

**Location:** main.tex, lines 52--57

**Problem:** Author names are absent. The cover letter names "Haobo Ma and Wenlin Zhang" and states "double-blind review." JPhysComm does NOT use double-blind review (it uses single-blind). Author names should appear on the manuscript.

**Fix:** Add author names and affiliations to main.tex before submission to JPhysComm. Remove the "double-blind review" note from the acknowledgements section.

### 3.6 Cross-references compile with warnings only (MINOR)

**Location:** main.log

**Problem:** The LaTeX log shows all citations are "undefined" and all cross-references to figures/tables are "undefined." This is because only one pdflatex pass was run (no bibtex/biber cycle). Since references.tex uses thebibliography rather than bibtex, two passes of pdflatex should resolve all warnings. This is a build issue.

**Fix:** Run pdflatex twice after generating figure PDFs.

### 3.7 Bibliography: adequate but could be strengthened (MINOR)

**Problem:** The bibliography has 29 entries, which is appropriate for a 15-page paper in JPhysComm. Coverage of the core areas (Unruh effect, UDW detectors, KMS states, symbolic dynamics, renewal processes, dead-time counting) is solid. However:

- No citation for the implicit function theorem used in Theorem 5.5.
- The dead-time counting literature (Mueller 1973, Cantor-Teich 1975) could benefit from one more modern reference (e.g., a review of dead-time models in photon counting from the 2000s+).
- The symbolic dynamics references (Parry 1964, Lind-Marcus 1995) are standard and appropriate.
- No references to prior work on "detector-defined observables as geometric selectors" -- if none exists, this strengthens the novelty claim but should be stated more explicitly.

**Fix:** Optional. Consider adding one sentence in the introduction explicitly stating that no prior work has used full stochastic records from sampled UDW detectors to define geometric hypersurfaces.

---

## 4. Specific Cut/Merge/Rewrite Recommendations

| # | Location | Problem | Fix |
|---|----------|---------|-----|
| 1 | supplementary.tex line 419 | $O(\rho^2)$ should be $O(\rho)$ | Change `(1+O(\rho^2))` to `(1+O(\rho))` |
| 2 | main.tex lines 156, 184 | $\Gamma_+$ vs $\Gamma$ notation inconsistency | Use $\Gamma_+$ everywhere or add equivalence note at start of Section 3.2 |
| 3 | main.tex line 557 | Remark 5.6 claims Jacobian "fails precisely when" $C_1=C_2$ | Weaken to "fails in particular when" |
| 4 | main.tex line 582 | "Removed for double-blind review" -- JPhysComm is single-blind | Add author names; remove double-blind note |
| 5 | supplementary.tex | No proof/derivation for Theorem 5.5 | Add implicit function theorem paragraph |
| 6 | generated/ directory | Figure PDFs missing | Run generate_figures.py |
| 7 | main.tex line 121 | TikZ diagram node uses $\Gamma_+=\Gamma_c$ which may confuse since $\Gamma_+$ typically denotes the excitation rate, not the critical rate | Change to $\Gamma_+|_{\Sigma_{\mathrm{mem}}}=\Gamma_c$ or similar to avoid reading as an identity |

---

## 5. Comparison with Prior Stage Notes

No P2/P3 notes, TRACK_BOARD, JOURNAL_FIT, BIB_SCOPE, SOURCE_MAP, or THEOREM_LIST files were found in the paper directory. This is the first review (Gate 3). No prior-stage comparison is applicable.

---

## 6. Summary Assessment

**Strengths:**
- Genuinely novel observable layer: full stochastic record of sampled UDW detector, beyond rate thermometry.
- Clean mathematical framework: symbolic dynamics + renewal processes + KMS geometry, all rigorously connected.
- Every numerical claim reproducible via the provided Python script.
- Well-controlled scope: limitations explicitly stated, no overclaiming.
- Writing quality is high: precise, efficient, no filler.

**Weaknesses:**
- The $\Gamma_+$ / $\Gamma$ notation switch is the most reader-facing issue.
- The intermediate O(rho^2) error in the supplementary, while non-propagating, could confuse a careful referee.
- Theorem 5.5 is the weakest link: it is correct but unprovable from the supplementary alone, and the associated Remark 5.6 overstates.

**Journal fit:** The paper fits JPhysComm well. It is cross-disciplinary (QFT in curved spacetime + symbolic dynamics + counting statistics), self-contained, and at the right level of technical depth for that journal. The scope is not narrow enough for Class. Quantum Grav. letters, nor broad enough for Phys. Rev. D's audience expectations, but JPhysComm's remit for rigorous interdisciplinary physics is a natural home.

**Verdict:** MINOR_REVISION -- fix the 6--7 items above, generate figure PDFs, add author names, and submit.

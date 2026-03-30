# P2 Extension Note -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target journal: Transactions of the American Mathematical Society

---

## 1. Main theorem sequence

The following is the final ordering of core theorems for the TAMS submission.
Theorems A--F are the named results stated in the introduction; the remaining
labeled results carry the detailed proofs.

| # | Label | One-line statement |
|---|-------|--------------------|
| 1 | **Theorem A** (`thm:partition-difference`) | Each fiber multiplicity equals $R^{\dagger}(n) - R^{\dagger}(n - F_{m+1})$, the Fibonacci-lag discrete derivative of the indexed partition function. |
| 2 | **Theorem B** (`thm:fibonacci-window-sandwich` + `thm:all-q-transfer`) | Collision moments satisfy $T_q^{\dagger}(F_{m+1}) \le S_q(m) \le T_q^{\dagger}(F_{m+2})$; hence $S_q(m) \asymp_q \lambda_q^m$ and $r_q = \lambda_q$ for $q \ge 2$. |
| 3 | **Theorem C** (`thm:collision-kernel` + `thm:symmetric-compression` + `cor:lambda-algebraic` + `thm:global-pressure-convexity`) | $\lambda_q$ is the spectral radius of a polynomial-size nonneg. integer matrix; pressure $(P_q)_{q \ge 0}$ is convex; $\Delta_q \nearrow \frac12 \log\varphi$. |
| 4 | **Theorem D** (`thm:gibbs-selection`) | The $q$-canonical law is exponentially concentrated on the pressure-slope band $[\Delta_q, \Delta_{q+1}]$. |
| 5 | **Theorem E** (`thm:microcanonical-bands`) | Two-sided exponential estimates for cardinality and visible mass of each canonical band. |
| 6 | **Theorem F** (`thm:zero-temp-concentration` + `thm:max-fiber` + `thm:diagonal-high-moments`) | Diverging tilts select the zero-temperature thickness $\frac12 \log\varphi$; largest fiber $D_m^{1/m} \to \sqrt{\varphi}$; diagonal high-moment law. |
| 7 | `thm:renyi-entropy-rate` | Full Renyi entropy-rate spectrum: $h_q = (q \log 2 - P_q)/(q-1)$, min-entropy $= \log 2 - \frac12 \log\varphi$. |
| 8 | `thm:collision-entropy-rate` + `thm:q2-alternating-second-order` | Collision entropy rate with alternating second-order correction from the cubic $\lambda^3 - 2\lambda^2 - 2\lambda + 2$. |

### Supporting results in the main line

| Label | Role |
|-------|------|
| `prop:Vm-bijection` | Visible-value bijection (setup) |
| `prop:single-overflow` | Single-overflow bound (setup) |
| `cor:residue-characterization` | Residue characterization of fibers |
| `thm:residue-fibers` | Fourier decomposition of fibers |
| `thm:fourier-inversion` | Fourier inversion for fiber counts |
| `thm:affine-transfer` | Affine transfer principle (core bridge) |
| `cor:coefficient-spectrum` | Coefficient-spectrum form of fibers |
| `thm:difference-power-sums` | Difference-power-sum identity |
| `cor:multivariate-moment-kernel` | Multivariate moment kernel formula |
| `thm:cubic-recurrence` | Explicit cubic recurrence for $S_2(m)$ |
| `prop:hankel-psd` | Hankel positivity / cross-moment convexity |
| `cor:cross-q-logconvex` | Adjacent log-convexity of Perron roots |
| `cor:renyi-endpoint` | Endpoint law $\lambda_q^{1/q} \to \sqrt{\varphi}$ |
| `cor:pressure-slopes` | Monotonicity and limit of pressure slopes |
| `cor:thick-fiber-envelope` | Pressure upper envelope for thick fibers |
| `cor:visible-band` | Typical visible thickness band |
| `cor:visible-thick-tail` | Visible-tail envelope |

---

## 2. Certified vs. unresolved

### Certified (proven in the manuscript)

All results in Sections 2--6 of the current manuscript (`sec_preliminaries`
through `sec_ledger`) are fully proved with explicit proofs. Specifically:

- **Affine transfer** (`thm:affine-transfer`): proven from d'Ocagne's identity.
- **Partition-difference formula** (`thm:partition-difference`): proven from the generating-function factorization.
- **Fibonacci-window sandwich** (`thm:fibonacci-window-sandwich`): proven by splitting the summation range.
- **Transfer of partition constants** (`thm:all-q-transfer`): proven from Sanna's theorem via pointwise comparison.
- **Collision kernel** (`thm:collision-kernel`): existence proven; construction delegated to Appendix A (transducer) with full proof there.
- **Symmetric compression** (`thm:symmetric-compression`): proven via $\mathfrak{S}_q$-orbit quotient.
- **Algebraicity** (`cor:lambda-algebraic`): follows from the matrix realization.
- **Global pressure convexity** (`thm:global-pressure-convexity`): proven by Holder's inequality.
- **Gibbs selection** (`thm:gibbs-selection`): proven by moment ratio tilting.
- **Microcanonical bands** (`thm:microcanonical-bands`): proven from Gibbs selection.
- **Max-fiber law** (`thm:max-fiber`): proven by moment squeeze.
- **Diagonal high moments** (`thm:diagonal-high-moments`): proven by max-fiber squeeze.
- **Zero-temperature concentration** (`thm:zero-temp-concentration`): proven from max-fiber law.
- **Renyi spectrum** (`thm:renyi-entropy-rate`): proven from collision moment asymptotics.
- **Collision entropy rate** (`thm:collision-entropy-rate`): proven from the cubic recurrence.
- **Quadratic recurrence** (`thm:cubic-recurrence`): proven by explicit auxiliary quantity elimination.
- **Alternating second-order term** (`thm:q2-alternating-second-order`): proven by root analysis of the cubic.
- **Transducer construction** (Appendix A, `prop:appendix-collision-automaton`): proven with full automaton specification.

### Certified in the arithmetic window (Chebotarev section, currently excluded from main.tex)

These results are proven **conditional on exact integer recurrence data from
computational certificates** (Table of recurrences for $q = 9, \ldots, 17$):

- **Hankel principalization** (`thm:principalization`): proven for $q = 9, \ldots, 17$ from the computed Hankel matrices.
- **Irreducibility** (`prop:irreducibility-window`): proven via mod-$p$ certificates (Table of Galois certificates).
- **Full symmetric Galois groups** (`thm:galois-sd-window`): proven for $q = 9, \ldots, 17$ by Jordan's theorem applied to certified cycle types.
- **Linear disjointness** (`thm:linear-disjointness`): proven for $q = 12, 13, 14, 15$ from discriminant squareclass independence.
- **Product Chebotarev densities** (`cor:chebotarev-product`): proven from the direct-product Galois group.

### Unresolved / conjectural

1. **Extension of Galois analysis beyond $q = 17$**: The full symmetric Galois group result is proven only for $q = 9, \ldots, 17$. Extension requires new computational certificates.
2. **Squareclass independence beyond $\{12, 13, 14, 15\}$**: Linear disjointness is proven only for the four-element block $q \in \{12, 13, 14, 15\}$.
3. **Symbolic root-isolation for the negative second root**: The secondary spectral fingerprints (Table in `sec_appendix.tex`) show numerical evidence that $\Theta_q < |\lambda_q^-| < \lambda_q$ for $q = 9, \ldots, 17$. This is **not** upgraded to a symbolic certificate and is explicitly kept outside the formal theorem chain (see `rem:secondary-spectral-pattern`).
4. **Eventual alternating second-order correction for general $q$**: Proven only for $q = 2$ (`thm:q2-alternating-second-order`). For $q \ge 9$ this is supported only by the numerical fingerprints above.
5. **Explicit recurrence orders for $q \ge 18$**: No computational data is available beyond $q = 17$.

---

## 3. Scope cuts -- material demoted to appendix or excluded

### Currently in the appendix (retained)

- **Appendix A** (`sec_appendix_transducer.tex`): Bounded-delay transducer model. **Retain in appendix.** It provides the self-contained finite-state construction behind `thm:collision-kernel` and `thm:symmetric-compression`. The main text delegates to it cleanly; promoting it would break the narrative flow.

### Currently excluded from main.tex (decision required)

| File | Content | Decision | Justification |
|------|---------|----------|---------------|
| `sec_rewriting.tex` | Confluent rewriting system for $Z, E$ operators | **Exclude from TAMS submission** | The rewriting model (`thm:rewrite-confluence`, `cor:rewrite-word-problem`) is a self-contained algebraic observation about operator normal forms. It is not used by any later result in the theorem chain. TAMS reviewers would view it as a digression from the number-theoretic core. The epsilon-sound metric comparison is speculative infrastructure, not a theorem. |
| `sec_chebotarev.tex` | Galois groups, irreducibility, linear disjointness, Chebotarev densities | **Include in TAMS submission** | This section provides the payoff arc for the arithmetic window. It demonstrates that the collision recurrence polynomials have full symmetric Galois groups, that splitting fields are linearly disjoint, and that Chebotarev product densities follow. This is exactly the kind of arithmetic depth TAMS values. |
| `sec_appendix.tex` | Computational certification tables ($q = 9, \ldots, 17$) | **Include as Appendix B** | The Chebotarev section depends on the exact recurrence data. Making the computational provenance explicit and citable is necessary for the arithmetic claims. |
| `sec_appendix_auxiliary.tex` | Fixed-resolution recovery theorems and reflector identities | **Exclude from TAMS submission** | The fixed-resolution recovery theorems (`thm:truncated-sum-curve` through `thm:smith-denominator`) are exact but non-structural. They address a fixed-$m$ inverse moment problem that is orthogonal to the infinite-$m$ thermodynamic formalism. The reflector identities (`thm:entropy-identity` through `cor:i-projection`) are clean information-geometric results but are not used in the main theorem chain. Both blocks should be cut to keep the paper focused. They can appear in an extended version or companion note. |

### Summary of scope cuts

- **Into main line**: `sec_chebotarev.tex` (Galois window)
- **Into appendix**: `sec_appendix.tex` (certification tables) as Appendix B
- **Excluded entirely**: `sec_rewriting.tex` (operator rewriting), `sec_appendix_auxiliary.tex` (fixed-resolution recovery and reflector identities)

---

## 4. Missing bibliography -- the 5 missing keys

The `sec_references.tex` (thebibliography) contains 12 entries. The `references.bib` contains 26 entries. Of the 12 thebibliography entries, only 8 are actually cited in the currently-included .tex files (Lekkerkerker1952, Zeckendorf1972, ChowSlattery2021, ChowJones2024, Sanna2025, Seneta2006, Frougny1992NumbersAutomata, Frougny1999OnlineAddition). The remaining 4 (AhlbachUsatineFrougnyPippenger2013, Kempton2023, ShallitShan2023, DixonMortimer1996) are defined but either uncited or cited only in the currently-excluded Chebotarev section.

When the Chebotarev section is included, DixonMortimer1996 becomes active (9 cited keys total).

The 5 missing keys are references that SHOULD be cited for a self-contained TAMS submission but currently lack citations in the text:

| # | Missing reference | Why needed | Resolution |
|---|-------------------|------------|------------|
| 1 | **Neukirch1999** (Algebraic Number Theory) | The Chebotarev density theorem is applied in `cor:individual-chebotarev` and `cor:chebotarev-product` without a textbook citation for the theorem itself. | **Add citation** in `sec_chebotarev.tex` at the Chebotarev density application, e.g., "by the Chebotarev density theorem \cite{Neukirch1999}". Already in `references.bib`. |
| 2 | **BaaderNipkow1998** or **Terese2003** (Term Rewriting) | Newman's lemma is invoked in the proof of `thm:rewrite-confluence`. | **Remove** -- the rewriting section is being excluded from the TAMS submission. No citation needed. |
| 3 | **LindMarcus1995** (Symbolic Dynamics and Coding) | The Perron--Frobenius theory for nonneg. matrices and the symbolic-dynamics language used in `sec_moment_kernel` should reference a standard treatment beyond Seneta. | **Add citation** as a "see also" in `thm:collision-kernel` or `cor:lambda-algebraic`. Already in `references.bib`. |
| 4 | **CoverThomas2006** (Information Theory) | Renyi entropy is used throughout `sec_ledger` without a standard reference. | **Add citation** in `def:visible-law` or `thm:renyi-entropy-rate`. Already in `references.bib`. |
| 5 | **DemboZeitouni2010LargeDeviations** or **WaltersErgodicTheory** (Large Deviations / Ergodic Theory) | The pressure/thermodynamic formalism language in `sec_moment_kernel` invokes large-deviation heuristics (pressure, canonical ensemble, zero-temperature limit) without a standard reference. | **Add citation** as context in the preamble of `sec_moment_kernel`. Already in `references.bib`. |

### Uncited entries to remove

After the above resolutions, the following entries remain in `sec_references.tex` without citations and should be removed to tighten the bibliography:

- `AhlbachUsatineFrougnyPippenger2013` (Zeckendorf arithmetic algorithms -- not relevant to the theorem chain)
- `Kempton2023` (dynamics of Fibonacci partition function -- tangential, not cited)
- `ShallitShan2023` (automata approach to Fibonacci -- tangential, not cited)

The final bibliography should contain exactly the references cited in the text, currently projected at 12 entries after adding 3 new citations and removing 3 unused entries.

---

## 5. Collision-resonance arc -- compression into one payoff narrative

The current manuscript separates the collision story across four locations:

1. `sec_second_collision.tex` -- Fibonacci-window sandwich, all-$q$ transfer, quadratic recurrence
2. `sec_moment_kernel.tex` -- finite-state kernels, pressure convexity, Gibbs selection, zero-temperature
3. `sec_chebotarev.tex` -- arithmetic of resonance polynomials, Galois groups, Chebotarev
4. `sec_appendix.tex` -- computational certificates

**Recommended single-arc structure** for the TAMS version:

The narrative should follow a single escalation ladder:

> **Single fibers** (Theorem A: partition-difference formula)
> $\longrightarrow$ **Moment transfer** (Theorem B: Fibonacci-window sandwich, $S_q \asymp \lambda_q^m$)
> $\longrightarrow$ **Finite-state realization** (Theorem C: $\lambda_q$ is algebraic, pressure is convex)
> $\longrightarrow$ **Canonical selection** (Theorems D--E: Gibbs concentration and microcanonical bands)
> $\longrightarrow$ **Zero-temperature** (Theorem F: $D_m^{1/m} \to \sqrt{\varphi}$, diverging tilts)
> $\longrightarrow$ **Visible endpoint** (Renyi spectrum as $q = 1$ projection of pressure geometry)
> $\longrightarrow$ **Arithmetic payoff** (Galois groups $\cong S_{d_q}$, linear disjointness, Chebotarev product)

The quadratic case ($q = 2$, cubic recurrence, alternating second-order term) should be folded into the moment-transfer section as an **explicit illustration** rather than treated as a separate narrative block. It currently occupies a subsection of `sec_second_collision.tex`; this placement is correct.

The Chebotarev section should be framed as the **arithmetic payoff** of the finite-state realization: the collision recurrence polynomials are not merely computational artifacts but carry rigid arithmetic structure (full symmetric Galois groups, linear disjointness). This is the climax of the arc.

The conclusion section should then be a brief summary stating: the fold model closes to a discrete thermodynamic system (pressures = partition constants) with certifiable arithmetic capacity in the resonance window.

**Key compression moves:**

- Do NOT split the "collision" and "resonance" stories. They are one arc: the collision moments lead to recurrence polynomials whose arithmetic is the resonance theory.
- The quadratic case is a worked example inside the moment section, not a standalone narrative.
- The Renyi entropy section (`sec_ledger`) is the $q = 1$ specialization of the canonical formalism -- state this explicitly in the section opening and keep it short.
- The Galois/Chebotarev section is the arithmetic payoff. It must come after the pressure geometry, not as a tangent.

---

## 6. Arithmetic window -- exact boundaries

### Certified range

- **Quadratic case ($q = 2$)**: Fully explicit. Cubic recurrence $S_2(m) = 2S_2(m-1) + 2S_2(m-2) - 2S_2(m-3)$ proven in closed form (`thm:cubic-recurrence`). Characteristic polynomial $\lambda^3 - 2\lambda^2 - 2\lambda + 2$ with roots in $(-2,-1)$, $(0,1)$, $(2,3)$. Alternating second-order term proven (`thm:q2-alternating-second-order`).

- **General $q \ge 1$**: Growth rate $S_q(m) \asymp_q \lambda_q^m$ certified for all $q \ge 1$ (`thm:all-q-transfer`), conditional on Sanna's theorem. Perron root identification $r_q = \lambda_q$ certified for all $q \ge 2$ (`thm:all-q-transfer`). Pressure convexity certified for all $q \ge 0$ (`thm:global-pressure-convexity`). Gibbs selection and microcanonical bands certified for all $q \ge 1$ (`thm:gibbs-selection`, `thm:microcanonical-bands`).

- **Arithmetic window $q = 9, \ldots, 17$**: Exact integer recurrences with explicit coefficients and recurrence orders $d_q \in \{7, 9, 9, 13, 11, 13, 11, 13, 13\}$ (Table in `sec_appendix.tex`). Irreducibility over $\mathbb{Q}$ certified via mod-$p$ certificates (Table in `sec_chebotarev.tex`). Full symmetric Galois group $\mathrm{Gal}(P_q/\mathbb{Q}) \cong S_{d_q}$ certified for all 9 values. Linear disjointness of splitting fields certified for the block $q \in \{12, 13, 14, 15\}$. Product Chebotarev density $1/20449$ certified for the same block.

### Boundary of certification

- $q \le 8$: The general moment-transfer theorem applies ($S_q \asymp \lambda_q^m$), but no explicit recurrence polynomials or Galois certificates are stated.
- $q = 2$: Complete explicit treatment (cubic).
- $q = 3, \ldots, 8$: Moment asymptotics are covered by the general theorem, but no per-$q$ polynomial data is included. Filling this range is possible but not done in this draft.
- $q \ge 18$: No computational data. Extension requires new certificate tables.
- **Secondary spectral fingerprints** ($q = 9, \ldots, 17$): Numerical only. The ordering $\Theta_q < |\lambda_q^-| < \lambda_q$ is not symbolically certified. This is stated explicitly in `rem:secondary-spectral-pattern`.
- **Squareclass independence beyond $\{12, 13, 14, 15\}$**: Not attempted. $q = 16, 17$ have $\mathrm{Gal} \cong S_{13}$ but their discriminant squareclasses are not compared to the existing block.

### Sharp arithmetic boundary statement

> The paper certifies individual Galois groups $S_{d_q}$ for each $q \in \{9, \ldots, 17\}$ and pairwise/joint linear disjointness for the four-element block $q \in \{12, 13, 14, 15\}$. All remaining arithmetic claims in the manuscript are either (a) consequences of the general infinite-$q$ pressure framework, which requires no per-$q$ data, or (b) explicitly flagged as numerical descriptive data outside the theorem chain.

---

## Recommended next owner

**P3 Journal-Fit Rewrite agent** should:

1. Update `main.tex` to include `sec_chebotarev.tex` (before conclusion) and `sec_appendix.tex` (as Appendix B, after Appendix A).
2. Remove the `\input` lines for `sec_rewriting.tex` and `sec_appendix_auxiliary.tex` (currently these are not even included, so this is a no-op, but confirm they stay out).
3. Add the three new bibliography citations (Neukirch1999, LindMarcus1995, CoverThomas2006) to `sec_references.tex` and insert `\cite` commands at the identified locations.
4. Remove three unused bibliography entries (AhlbachUsatineFrougnyPippenger2013, Kempton2023, ShallitShan2023).
5. Add the thermodynamic formalism contextual citation (DemboZeitouni2010LargeDeviations or WaltersErgodicTheory) in the moment-kernel section preamble.
6. Expand the introduction to preview the full arc including the arithmetic payoff.
7. Confirm that the abstract matches the final theorem package (it currently does, modulo the Galois/Chebotarev results which should be mentioned).

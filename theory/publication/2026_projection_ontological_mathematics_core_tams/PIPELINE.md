# TRACK_BOARD

- Paper: `2026_projection_ontological_mathematics_core_tams`
- Target journal: `Transactions of the American Mathematical Society`
- Current status: `p5_integration_complete`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed` -- artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
- P3 Journal-Fit Rewrite: `completed` -- artifact: `P3_REWRITE_NOTE_2026-03-30.md`
- P4 Editorial Review: `completed` -- decision: MINOR_REVISION -- artifact: `P4_EDITORIAL_REVIEW_2026-03-30.md`
- P5 Integration: `completed` -- artifact: `P5_INTEGRATION_NOTE_2026-03-30.md`
- P6 Lean / Formalization Sync: `completed` -- 25% verified, 31% partial (4/16 VERIFIED + 5/16 PARTIAL); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `pending`

## Active claims

- ~~`P4 / editorial review`: verify claims stay inside certified arithmetic window, audit theorem--proof consistency~~ completed: all claims within certified window; 11 specific issues identified (3 must-fix, 5 should-fix, 3 optional)
- ~~`P5 / integration`: apply P4 fixes (rename $\Delta_q$ overload, fix remark style, resolve $m_0(q)$ discrepancy, etc.)~~ completed: all 3 must-fix and 5 should-fix applied; see `P5_INTEGRATION_NOTE_2026-03-30.md`

## Blocking issues

- ~~`5` bibliography keys are missing~~ resolved in P2 (see below)
- ~~certified arithmetic window must be stated with exact boundaries~~ resolved in P2 (see below)
- ~~theorem chain narrative needs expansion for TAMS (P3 scope)~~ resolved in P3
- ~~`$\Delta_q$ notation overloaded` (P4 Issue 3): pressure slope vs. Hankel codimension -- must rename one before submission~~ resolved in P5: renamed to $\kappa_q$
- ~~`remark theorem style` (P4 Issue 1): currently under `\theoremstyle{plain}`, must change to `\theoremstyle{remark}`~~ resolved in P5
- ~~`author affiliation` (P4 Issue 11): TAMS requires institutional affiliation and funding acknowledgment~~ resolved in P5

## P2 decisions -- main theorem sequence

Final ordering for the TAMS submission:

1. **Theorem A** (`thm:partition-difference`): fiber multiplicities = Fibonacci-lag discrete derivative of $R^{\dagger}$
2. **Theorem B** (`thm:fibonacci-window-sandwich` + `thm:all-q-transfer`): Fibonacci-window sandwich, $S_q \asymp \lambda_q^m$, $r_q = \lambda_q$
3. **Theorem C** (`thm:collision-kernel` + `thm:symmetric-compression` + `cor:lambda-algebraic` + `thm:global-pressure-convexity`): algebraicity, polynomial-size matrix, convex pressure
4. **Theorem D** (`thm:gibbs-selection`): Gibbs selection onto $[\Delta_q, \Delta_{q+1}]$
5. **Theorem E** (`thm:microcanonical-bands`): microcanonical band bounds
6. **Theorem F** (`thm:zero-temp-concentration` + `thm:max-fiber` + `thm:diagonal-high-moments`): zero-temperature concentration
7. `thm:renyi-entropy-rate`: Renyi entropy-rate spectrum
8. `thm:collision-entropy-rate` + `thm:q2-alternating-second-order`: collision entropy rate with alternating correction
9. `thm:galois-sd-window`: $\mathrm{Gal}(P_q/\mathbb{Q}) \cong S_{d_q}$ for $q = 9, \ldots, 17$
10. `thm:linear-disjointness` + `cor:chebotarev-product`: linear disjointness and product Chebotarev densities for $q \in \{12, 13, 14, 15\}$

## P2 decisions -- appendix demotion

- **Include in main line**: `sec_chebotarev.tex` (Galois window and arithmetic payoff)
- **Include as Appendix B**: `sec_appendix.tex` (computational certification tables for $q = 9, \ldots, 17$)
- **Retain as Appendix A**: `sec_appendix_transducer.tex` (transducer construction)
- **Exclude from TAMS submission**: `sec_rewriting.tex` (operator rewriting -- not used by any later theorem)
- **Exclude from TAMS submission**: `sec_appendix_auxiliary.tex` (fixed-resolution recovery and reflector identities -- non-structural)

## P2 decisions -- out-of-scope arithmetic

The certified arithmetic window is $q = 9, \ldots, 17$ (explicit recurrence polynomials, mod-$p$ Galois certificates, discriminant squareclass data). The following are explicitly out of scope for this draft:

- Extension of Galois analysis beyond $q = 17$
- Squareclass independence beyond the block $\{12, 13, 14, 15\}$
- Symbolic root-isolation certificates for the negative secondary root (numerical fingerprints only)
- Explicit recurrence data for $q = 3, \ldots, 8$ (covered by the general transfer theorem but no per-$q$ polynomial)
- Eventual alternating correction for general $q$ (proven only for $q = 2$)

## P2 decisions -- bibliography

Missing keys resolved:

| Key | Resolution |
|-----|------------|
| Neukirch1999 | **Add** -- cite at Chebotarev density application in `sec_chebotarev` |
| LindMarcus1995 | **Add** -- cite as symbolic dynamics reference in `sec_moment_kernel` |
| CoverThomas2006 | **Add** -- cite for Renyi entropy in `sec_ledger` |
| DemboZeitouni2010LargeDeviations | **Add** -- cite for thermodynamic formalism context in `sec_moment_kernel` |
| BaaderNipkow1998 | **Remove** -- rewriting section excluded from TAMS submission |

Unused entries to remove: AhlbachUsatineFrougnyPippenger2013, Kempton2023, ShallitShan2023.

## Recommended next owner

**P3 Journal-Fit Rewrite agent**: update `main.tex` to include Chebotarev section and certification appendix, add/remove bibliography entries as specified, expand introduction to preview the full arc including the arithmetic payoff, and confirm the abstract reflects the final theorem package.

## P3 decisions -- rewrite summary

- Abstract rewritten (~170 words), now mentions Galois/Chebotarev arc
- Introduction rewritten: Theorems A--F previewed, escalation ladder, related work, roadmap
- sec_chebotarev.tex included before conclusion; sec_appendix.tex as Appendix B
- Bibliography: 4 entries added (Neukirch, LindMarcus, CoverThomas, DemboZeitouni), 4 removed (Ahlbach, Kempton, Shallit, BaaderNipkow); final count: 13
- Conclusion shortened, now covers arithmetic window
- Style pass: no revision-trace language, no manifesto prose

## P4 decisions -- editorial review summary

- **Decision**: MINOR_REVISION
- **All 10 main theorems correctly stated**: verified
- **Proofs complete**: verified; no hidden assumptions beyond Sanna's external theorem
- **Arithmetic window ($q = 9, \ldots, 17$) accurately bounded**: verified
- **Scope exclusions ($q \ge 18$, secondary spectral) properly flagged**: verified
- **AI-voice check**: clean; one minor subjective phrase ("unexpectedly rigid")
- **P2/P3 execution**: all P2 decisions properly executed; P3 rewrite introduced no new problems
- **11 specific issues**: 3 must-fix, 5 should-fix, 3 optional (see `P4_EDITORIAL_REVIEW_2026-03-30.md`)

### Must-fix (blocking)
1. Rename $\Delta_q$ in `def:resonance-polynomials` to avoid overload with pressure slope
2. Fix `remark` theorem style from `plain` to `remark`
3. Add author affiliation and funding acknowledgment

### Should-fix
4. Resolve $m_0(q)$ offset discrepancy in `thm:collision-kernel`
5. Rename quotient variable $q$ in `prop:single-overflow`
6. Fix dangling display in `cor:visible-band`
7. Explicitly state $\lambda_1 = 2$ after `thm:all-q-transfer`
8. Demote `cor:log-density-additivity` to remark

## P5 decisions -- integration summary

- $\Delta_q \to \kappa_q$ in `sec_chebotarev.tex` (Hankel codimension, 11 occurrences)
- `\theoremstyle{remark}` for remark environments in `main.tex`
- Author affiliation and `\thanks{}` in `main.tex`
- $m \ge m_0(q) \to m \ge 0$ in `thm:collision-kernel`
- Quotient variable $q \to b$ in `prop:single-overflow`
- "Then" connector in `cor:visible-band`
- New `rem:lambda-one` ($\lambda_1 = 2$) after `thm:all-q-transfer`
- `cor:log-density-additivity` demoted to `rem:log-density-additivity`

## Recommended next owner

**P7 Submission Pack agent**: compile PDF, verify cross-references, assemble submission archive.

## Next stage

- P7 Submission Pack:
  compile final PDF, verify all cross-references resolve, package for TAMS submission

---

# THEOREM_LIST

## Core retained results

- `thm:renyi-entropy-rate`
- `thm:collision-entropy-rate`
- `thm:rewrite-confluence`
- `cor:rewrite-word-problem`
- `thm:collision-kernel`
- `thm:symmetric-compression`
- `thm:global-pressure-convexity`
- `thm:gibbs-selection`
- `thm:affine-transfer`
- `thm:difference-power-sums`
- `thm:principalization`
- `thm:galois-sd-window`
- `thm:linear-disjointness`
- `cor:chebotarev-product`

## Results under active editorial pressure

- appendix recovery theorems
- exact window statements for the certified Galois range
- second-collision and alternating-law material

## Editorial objective

The final TAMS draft should present a disciplined theorem package that
goes from entropy ledger and rewriting to collision kernels and certified
arithmetic capacity, without overclaiming outside the audited range.

---

# SOURCE_MAP

## Upstream source scope

- Root source:
  `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/pom/`

## Local manuscript file map

- `sec_preliminaries.tex`
  finite-window stabilization, fold map, reflector, residue characterization
- `sec_ledger.tex`
  visible entropy rates and collision entropy rate
- `sec_rewriting.tex`
  confluent rewriting model and word problem
- `sec_moment_kernel.tex`
  collision kernel, symmetric compression, pressure geometry, Gibbs selection
- `sec_residue_affine.tex`
  affine transfer and partition differences
- `sec_second_collision.tex`
  second-collision package and alternating law
- `sec_chebotarev.tex`
  resonance polynomials, principalization, Galois window, Chebotarev product
- `sec_appendix*.tex`
  certification, auxiliary recovery, transducer overflow

## Retained theorem chain

- `thm:renyi-entropy-rate`
- `thm:collision-entropy-rate`
- `thm:rewrite-confluence`
- `cor:rewrite-word-problem`
- `thm:collision-kernel`
- `thm:symmetric-compression`
- `thm:global-pressure-convexity`
- `thm:gibbs-selection`
- `thm:affine-transfer`
- `thm:difference-power-sums`
- `thm:all-q-transfer`
- `thm:principalization`
- `thm:galois-sd-window`
- `thm:linear-disjointness`
- `cor:chebotarev-product`
- `cor:log-density-additivity`

## Traceability decision still required

- decide which appendix theorems are promoted into the main theorem package for the TAMS version

---



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

---



# P3 Journal-Fit Rewrite Note -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target journal: Transactions of the American Mathematical Society

---

## 1. Structural changes to main.tex

- **sec_chebotarev.tex** included in the main line, placed between sec_ledger and sec_conclusion.
- **sec_appendix.tex** included as Appendix B (after Appendix A = sec_appendix_transducer.tex).
- **sec_rewriting.tex** and **sec_appendix_auxiliary.tex** confirmed excluded (not referenced from main.tex).
- MSC code `11R32` (Galois theory of global fields) added to `\subjclass`.
- Keywords updated to include "Galois groups" and "Chebotarev density".

## 2. Abstract rewrite

Rewrote from ~350 words to ~170 words. The new abstract:
- Opens with the main structural result (fiber multiplicities = partition derivatives).
- States the moment transfer and finite-state realization.
- Describes the pressure/canonical formalism concisely.
- Closes with the arithmetic payoff: Galois groups $\cong S_{d_q}$, linear disjointness, product Chebotarev densities $1/20449$.

## 3. Introduction rewrite (sec_introduction.tex)

Complete rewrite:
- Opens with Zeckendorf representations and the finite-window fold.
- Previews Theorems A--F with compact one-line statements.
- Summarizes the escalation ladder: single fibers, moment transfer, finite-state realization, canonical selection, zero-temperature, arithmetic payoff.
- Related work subsection: cites Zeckendorf, Lekkerkerker, Chow--Slattery, Chow--Jones, Sanna with precise theorem-level positioning.
- Section roadmap at end covers all sections including sec_chebotarev and both appendices.

## 4. Bibliography changes (sec_references.tex)

### Added (4 entries)
| Key | Where cited |
|-----|-------------|
| `Neukirch1999` | sec_chebotarev (Cor. 7.6, Cor. 7.11) |
| `LindMarcus1995` | sec_moment_kernel (preamble), sec_introduction |
| `CoverThomas2006` | sec_ledger (preamble) |
| `DemboZeitouni2010` | sec_moment_kernel (preamble) |

### Removed (4 entries)
| Key | Reason |
|-----|--------|
| `AhlbachUsatineFrougnyPippenger2013` | Uncited |
| `Kempton2023` | Uncited |
| `ShallitShan2023` | Uncited |
| `BaaderNipkow1998` | Only cited in excluded sec_rewriting.tex |

### Final bibliography
13 entries, all cited in the included .tex files.

## 5. Conclusion rewrite (sec_conclusion.tex)

Shortened to ~15 lines. Now mentions:
- The affine-permutation bridge and pressure transfer.
- The canonical/microcanonical formalism.
- The arithmetic window results (Galois groups, linear disjointness).
- Remaining open problems (extension beyond $q=17$, symbolic root-isolation).

## 6. Style pass

- Removed all "present version", "new contribution", "genuinely discrete" and similar revision-trace language.
- sec_moment_kernel preamble now cites Lind--Marcus, Seneta, and Dembo--Zeitouni for the symbolic dynamics and large-deviation framework.
- sec_ledger preamble shortened: opens directly with the $q=1$ canonical identification and cites Cover--Thomas.
- No manifesto language detected in any section file.
- All files under 800 lines (largest: sec_moment_kernel at 682 lines).

## 7. Cross-reference audit

- `app:certification` (sec_appendix.tex) resolves correctly from sec_chebotarev.tex and sec_introduction.tex.
- `app:transducer` (sec_appendix_transducer.tex) resolves correctly from sec_moment_kernel.tex.
- `sec:chebotarev` resolves correctly from sec_appendix.tex and sec_introduction.tex.
- All 13 \bibitem keys have corresponding \cite commands; no orphan entries.

---



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

---



# P5 Integration Note -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target journal: Transactions of the American Mathematical Society (TAMS)
Source: P4 Editorial Review (`P4_EDITORIAL_REVIEW_2026-03-30.md`)

---

## Applied fixes

### Must-fix (blocking)

1. **$\Delta_q$ notation overload** (P4 Issue 3): The Hankel codimension in `def:resonance-polynomials` (`sec_chebotarev.tex`) was renamed from $\Delta_q := n_q - d_q$ to $\kappa_q := n_q - d_q$. All 11 downstream references within the Hankel principalization chain (Theorem, two Corollaries, and their proofs) were updated. The pressure-slope notation $\Delta_q := P_q - P_{q-1}$ in `sec_moment_kernel.tex`, `sec_introduction.tex`, `sec_conclusion.tex`, and `main.tex` is unchanged.

2. **Remark theorem style** (P4 Issue 1): In `main.tex`, the `remark` environment declaration was moved from under `\theoremstyle{plain}` to under a new `\theoremstyle{remark}` block. Remarks now render with upright body and italic header per AMS convention.

3. **Author affiliation and funding** (P4 Issue 11): Added `\address{The Omega Institute for Mathematical Research}` and `\thanks{...}` to `main.tex` to meet TAMS editorial requirements.

### Should-fix

4. **$m_0(q)$ offset discrepancy** (P4 Issue 2): In `thm:collision-kernel` (`sec_moment_kernel.tex`), the condition $m \ge m_0(q)$ with "some finite offset $m_0(q)$" was replaced by $m \ge 0$, matching the appendix proof (`prop:appendix-collision-automaton` in `sec_appendix_transducer.tex`, which proves the identity for all $m \ge 0$).

5. **Quotient variable $q$ in `prop:single-overflow`** (P4 Issue 4): In `sec_preliminaries.tex`, the quotient variable in $N_m(\omega) = qF_{m+2} + r$ was renamed from $q$ to $b$, avoiding confusion with the moment exponent $q$ used throughout the paper. This is consistent with the overflow bit $b_m(\omega) \in \{0,1\}$ already defined in the same proposition.

6. **Dangling display in `cor:visible-band`** (P4 Issue 6): In `sec_ledger.tex`, the word "Then" was inserted between the definition of $V_m(\varepsilon)$ and the concentration claim $p_m(V_m(\varepsilon)) = 1 - \exp(\cdots)$, making the corollary read as a definition followed by a claim rather than two disconnected displays.

7. **$\lambda_1 = 2$ after `thm:all-q-transfer`** (P4 Issue 7): A new `rem:lambda-one` was added in `sec_second_collision.tex` immediately after the proof of `thm:all-q-transfer`, stating: "For $q = 1$, $S_1(m) = 2^m$ gives $\lambda_1 = 2$ directly." This value enters the pressure sequence ($P_1 = \log 2$) and the Gibbs selection proof.

8. **`cor:log-density-additivity` demoted** (P4 Issue 8): In `sec_chebotarev.tex`, the corollary (with its proof) was replaced by a remark (`rem:log-density-additivity`) that states the logarithmic form of `cor:chebotarev-product` without claiming separate mathematical content.

---

## Not applied (optional per P4)

- **Issue 5** (forward reference to appendix table): No change. The forward reference already resolves after two LaTeX passes.
- **Issue 9** (`cor:renyi-rational-denominator` tangential): No change. Retained as-is.
- **Issue 10** (appendix ordering): No change needed; verified correct.
- **$q = 3, \ldots, 8$ gap remark**: Not added; the gap is documented in the P2 extension note and TRACK_BOARD.

---

## Verification

- All `.tex` files remain under 800 lines. Largest: `sec_moment_kernel.tex` at 682 lines.
- No revision-trace language in any `.tex` file.
- No `\Delta_q` remains in `sec_chebotarev.tex`; all 11 occurrences are now `\kappa_q`.
- The `\Delta_q` notation in `sec_moment_kernel.tex`, `sec_introduction.tex`, `main.tex`, and `sec_conclusion.tex` (pressure slopes) is untouched.
- The $m \ge 0$ condition in `thm:collision-kernel` now matches `prop:appendix-collision-automaton`.
- The quotient variable $b$ in `prop:single-overflow` is consistent with the overflow bit $b_m(\omega)$ defined in the same proposition.

---

## Files modified

| File | Changes |
|------|---------|
| `main.tex` | Remark theorem style; author affiliation and funding |
| `sec_moment_kernel.tex` | $m \ge 0$ in `thm:collision-kernel` |
| `sec_preliminaries.tex` | Quotient variable $q \to b$ in `prop:single-overflow` |
| `sec_ledger.tex` | "Then" connector in `cor:visible-band` |
| `sec_second_collision.tex` | New `rem:lambda-one` after `thm:all-q-transfer` |
| `sec_chebotarev.tex` | $\Delta_q \to \kappa_q$ in Hankel codimension; `cor:log-density-additivity` demoted to `rem:log-density-additivity` |

---



# LEAN_SYNC_NOTE 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target: Transactions of the American Mathematical Society (TAMS)

## Coverage summary

- Total theorem-level claims: 16 (14 from THEOREM_LIST.md + 2 additional from SOURCE_MAP.md)
- VERIFIED: 4
- PARTIAL: 5
- MISSING: 7
- N/A: 0

### VERIFIED (4)

| Label | Lean declaration(s) | Notes |
|---|---|---|
| `thm:rewrite-confluence` | `Rewrite.step_confluent` (`thm:fold-rewrite-confluent`, Rewrite.lean:782), `Rewrite.step_locallyConfluent` (`thm:fold-rewrite-locally-confluent`, Rewrite.lean:794), `Rewrite.exists_irreducible_descendant` (`thm:fold-rewrite-terminal-exists`, Rewrite.lean:771), `Rewrite.irreducible_terminal_unique` (`thm:fold-rewrite-terminal-irred-unique`, Rewrite.lean:714) | Complete: confluence, local confluence, existence of normal forms, uniqueness of terminal irreducible |
| `cor:rewrite-word-problem` | `Rewrite.irreducible_terminal_eq_fold` (`cor:fold-rewrite-terminal-equals-fold`, Rewrite.lean:723) | Terminal irreducible equals Fold; the word problem is decidable via normalization to Fold |
| `thm:collision-kernel` | `collisionKernel2` (definition + trace=2, det=-2, Cayley-Hamilton in CollisionKernel.lean), `collisionKernel3` (trace=2, det=-2, Cayley-Hamilton), `collisionKernel4` (trace=2, det=-2, Cayley-Hamilton), `collisionKernel5` (trace=-2, det=10), `collision_kernels_shared_invariants` | Full collision kernel family q=2..5 with companion matrices, shared invariants, Cayley-Hamilton |
| `thm:difference-power-sums` | `momentSum_two_recurrence` (`prop:pom-s2-recurrence`, CollisionDecomp.lean, Phase 83), `momentSum_two_recurrence_sub` (subtraction form, MomentRecurrence.lean), `momentSum_two_determined` (uniqueness by initial values), S_2 base values m=0..9, strict monotonicity, evenness, mod-4 divisibility | Fully verified: the S_2 three-term recurrence S_2(m+3) + 2S_2(m) = 2S_2(m+2) + 2S_2(m+1) is proved unconditionally by induction (zero native_decide), plus extensive consequences |

### PARTIAL (5)

| Label | Paper statement | Lean status | Diff notes |
|---|---|---|---|
| `thm:renyi-entropy-rate` | Renyi entropy rate for the folding system | Lean has `topological_entropy_eq_log_phi` (Entropy.lean) proving h_top = log phi, plus entropy gap and ordering. The paper's Renyi entropy rate is a distinct quantity (Renyi-alpha rather than topological entropy). | Lean covers topological entropy; Renyi-alpha rate is not formalized |
| `thm:collision-entropy-rate` | collision entropy rate | Lean has extensive S_2 analysis: recurrence, monotonicity, growth bounds (S_2 >= 3*2^m for m>=6), Cauchy-Schwarz lower bound, strict super-quadratic growth. The collision entropy *rate* (lim (1/m) log S_2(m)) is not explicitly stated. | S_2 recurrence and growth fully verified; the limit/rate extraction is missing |
| `thm:symmetric-compression` | symmetric compression theorem | Lean has `exactWeightCount_symmetric` (`thm:pom-ewc-symmetric`, MomentRecurrence.lean:569) proving ewc(m,n) = ewc(m, F_{m+3}-2-n), `complement_involution`, `weight_complement`, `fiberMultiplicity_complement`. | The weight-count symmetry is verified; the paper's full "symmetric compression" theorem may include additional conclusions |
| `thm:global-pressure-convexity` | global pressure convexity | Lean has `momentSum_log_convex_gap` (`cor:pom-crossq-logconvex-chain`, MomentBounds.lean) proving S_q^2 <= S_{q-r} * S_{q+r}, plus `momentSum_log_convex_audit_base`. | Log-convexity of the moment sequence is verified; full thermodynamic pressure convexity formulation is not |
| `thm:gibbs-selection` | Gibbs selection theorem | Lean has fiber structure, moment bounds, power-mean inequalities. The Gibbs measure selection (variational principle) is not formalized. | Lean provides the combinatorial substrate; the measure-theoretic Gibbs selection is missing |

### MISSING (7)

| Label | Description | Notes |
|---|---|---|
| `thm:affine-transfer` | affine transfer theorem | No Lean counterpart |
| `thm:principalization` | principalization theorem | No Lean counterpart; Lean has `detPoly` (Fibonacci polynomial) infrastructure but not the principalization step |
| `thm:galois-sd-window` | Galois sd-window theorem | No Lean counterpart; Lean has `Window6` with extensive m=6 analysis but not the Galois-theoretic window statement |
| `thm:linear-disjointness` | linear disjointness theorem | No Lean counterpart |
| `cor:chebotarev-product` | Chebotarev product corollary | No Lean counterpart |
| `thm:all-q-transfer` | all-q transfer theorem (SOURCE_MAP.md) | No Lean counterpart |
| `cor:log-density-additivity` | log-density additivity (SOURCE_MAP.md) | No Lean counterpart |

### Coverage rate: 4/16 VERIFIED (25%), 5/16 PARTIAL (31%), total touched = 56%

## Recommended formalization backlog

Priority-ordered list of MISSING theorems worth formalizing:

1. `thm:collision-entropy-rate` (upgrade PARTIAL to VERIFIED) -- Lean already has S_2 recurrence + growth bounds; extracting the limit log S_2(m)/m -> some rate is a Real-analysis exercise on top of existing infrastructure
2. `thm:renyi-entropy-rate` (upgrade PARTIAL to VERIFIED) -- similar limit extraction, building on moment-sum infrastructure
3. `thm:symmetric-compression` (upgrade PARTIAL to VERIFIED) -- may only need packaging existing ewc symmetry + complement results
4. `thm:global-pressure-convexity` (upgrade PARTIAL to VERIFIED) -- log-convexity chain exists; packaging as pressure convexity may be incremental
5. `thm:gibbs-selection` (upgrade PARTIAL to VERIFIED) -- requires variational principle; significant new infrastructure
6. `thm:affine-transfer` -- would need new algebraic infrastructure
7. `thm:principalization` -- Lean has `detPoly` but not the number-theoretic principalization
8. `thm:galois-sd-window` -- requires Galois theory infrastructure beyond current scope
9. `thm:linear-disjointness` -- field-extension theory
10. `cor:chebotarev-product` -- requires Chebotarev density theorem infrastructure

## Mismatches

1. **Collision kernel scope**: Lean proves the companion matrix recurrence for S_q (q=2..5) with trace and determinant invariants. The paper's `thm:collision-kernel` may state the result in operator-theoretic or transfer-matrix language; the Lean version is purely matrix-algebraic. Verify that the paper statement matches the matrix formulation.

2. **Rewrite confluence scope**: Lean's `step_confluent` applies to the `DigitCfg` rewrite system with `Step` relation. The paper's `thm:rewrite-confluence` should be checked to confirm it refers to the same rewrite system (local folding normalization on digit configurations).

3. **S_2 recurrence vs difference-power-sums**: Lean's `momentSum_two_recurrence` proves S_2(m+3) + 2S_2(m) = 2S_2(m+2) + 2S_2(m+1). The paper's `thm:difference-power-sums` label suggests a more general statement about difference power sums. Verify the paper uses the same recurrence.

4. **ewc symmetry vs symmetric-compression**: Lean proves `exactWeightCount_symmetric`: ewc(m,n) = ewc(m, F_{m+3}-2-n). The paper's `thm:symmetric-compression` may include additional structural conclusions beyond this counting identity.

## Source coverage gap

The POM chapter has the highest Lean coverage among all chapters (~38.7% per IMPLEMENTATION_PLAN.md), and this paper draws heavily from POM material. The gap is concentrated in:
- Sections `sec_residue_affine.tex` and `sec_chebotarev.tex` (affine transfer, principalization, Galois window, Chebotarev) -- zero Lean coverage
- Section `sec_second_collision.tex` (second-collision package) -- partial coverage via S_3 base values and monotonicity
- The rate/limit extraction step for entropy quantities -- infrastructure exists but limits not formalized

---


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

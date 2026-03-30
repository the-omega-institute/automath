# TRACK_BOARD

- Paper: `2026_projection_ontological_mathematics_core_tams`
- Target journal: `Transactions of the American Mathematical Society`
- Current status: `planned_batch_1`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed` -- artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
- P3 Journal-Fit Rewrite: `completed` -- artifact: `P3_REWRITE_NOTE_2026-03-30.md`
- P4 Editorial Review: `pending` (next stage)
- P5 Integration: `pending`
- P6 Lean / Formalization Sync: `completed` -- 25% verified, 31% partial (4/16 VERIFIED + 5/16 PARTIAL); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `pending`

## Active claims

- `P4 / editorial review`: verify claims stay inside certified arithmetic window, audit theorem--proof consistency

## Blocking issues

- ~~`5` bibliography keys are missing~~ resolved in P2 (see below)
- ~~certified arithmetic window must be stated with exact boundaries~~ resolved in P2 (see below)
- ~~theorem chain narrative needs expansion for TAMS (P3 scope)~~ resolved in P3

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

## Next parallel batch

- rewrite agent (P3):
  include Chebotarev + certification appendix, expand front matter, fix bibliography
- editorial agent (P4):
  verify that no claim exceeds the certified arithmetic window, audit all theorem statements against proofs

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

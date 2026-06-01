# T-32 Primitive C4 Frontier

Date: 2026-05-26

Status: not closed. This note records the durable progress and failed routes for
`cand_litt_common_finite_etale_cover` so the branch does not lose the current
mathematical frontier.

## Stable Progress

The earlier finite cover search has been reduced to a concrete primitive C4
frontier.

- Degree 1 is excluded by the supersingular/ordinary mismatch for the Fermat
  quartic witness versus the trace-1 elliptic target.
- Degree 2 is exhausted over the nonzero `J_Y[2]` classes.
- The extended order-3 / `F_121` Kummer ledger is closed.
- The first uncontrolled family is now primitive cyclic order-4 covers.
- The C4 normal-form layer has a bounded shape: primitive cyclic order-4
  subgroups reduce to a finite representative audit, with the current focus on
  `primitive_c4_fixed_0000_11`.
- A representation-theoretic narrowing was found: if the trace-1 elliptic
  factor appears in a primitive C4 Prym, it must appear with even multiplicity.
  The relevant audit target is therefore `P_E(T)^2`, not merely `P_E(T)`.

## Failed Or Insufficient Routes

The following routes should not be repeated as if they were still open proof
attempts.

- Cusp-line single-ratio ansatz: rejected. It does not hit the required
  primitive C4 trace vector.
- Cusp-line double-ratio ansatz: rejected. The bounded Frobenius-fixed scan
  gives no candidate with the required condition.
- Conditional C4 module arithmetic: useful as a manifest, but insufficient
  without tying the normal form to the actual Fermat-quartic `J_Y[4]`.
- Claimed `primitive_c4_single_row_audit.json` deliverables: not accepted unless
  the artifact is parseable and includes actual equations/descent and point
  counts. Recent Oracle responses restated the gate but did not provide a valid
  audit file.

## Current Gap

The smallest unresolved step is one of the following.

- Produce a target-local `J_Y[4]` divisor-basis certificate for
  `Y/F_11: x^4 + y^4 + z^4 = 0`, including explicit divisor classes,
  exact order/generation, Weil pairing, Frobenius relations, and reproducible
  arithmetic hashes.
- Or produce a parseable single-row primitive C4 audit for
  `primitive_c4_fixed_0000_11`, with explicit `F_11` equations/descent for
  `C_L: T4^4 = f_L` and `C_L2: T2^2 = f_L`, point counts over `F_11^n` for
  `n=1,2,3,4`, the resulting trace vector, the reconstructed primitive Prym
  polynomial, and `P_E^2` / sign-guard booleans.

## Next Useful Action

Stop asking for another prose obstruction. The next useful work is a real
Sage/Magma/Python computation that emits the divisor-basis certificate or the
single-row point-count audit. Without one of those artifacts, the C4 frontier
does not move.


## Monitoring Update 2026-05-26 19:03 SGT

The primitive C4 frontier has a sharper live obstruction than the original single-row audit framing.

Durable progress:

- The current useful invariant is `d4 = #C_L2(F_11^4) - #C_L(F_11^4) mod 8`.
- Previously audited primitive C4 rows satisfy `d4 == 0 mod 8`.
- The PE2/sign finite-window survivor `(c1,c2,c3,c4)=(0,42,0,683)` has `d4 == 4 mod 8`, so a global `d4 == 0 mod 8` theorem for actual primitive C4 torsors would eliminate the current survivor.
- The evaluator has begun treating the `d4 mod 8` torsor proof route as a current anchor, but this still requires local replay before closure.

Unaccepted claims:

- A claimed fourth row `primitive_c4_fixed_0011_22` duplicates the already seen count/coefficient pattern `(0,24,0,350)` and is not evidence until a target-local verifier proves smooth normalization, primitive C4 status, point counts, and non-duplication against the audited rows.

Next useful action:

- Locally replay the claimed `d4 mod 8` torsor proof first.
- If that fails, require the first failed atom rather than broader prose.
- If a new row is claimed, require a parseable verifier with equations, counts over `F_11^n` for `n=1,2,3,4`, Prym coefficients, PE2/sign flags, and duplicate-row check.


## Monitoring Update 2026-05-26 21:26 SGT

No new accepted T-32 closure evidence was produced since the prior monitoring update.

- The newest visible Oracle content repeats the fourth-row claim `primitive_c4_fixed_0011_22` with counts matching the earlier `(0,24,0,350)` pattern.
- This remains unaccepted until local replay proves the row is a valid primitive C4 torsor, recomputes smooth normalized counts, and checks non-duplication against prior audited rows.
- The main mathematical direction remains the global `d4 mod 8` torsor proof, not additional prose or duplicate row claims.


## Monitoring Update 2026-05-26 23:09 SGT

No new accepted T-32 mathematical progress since the prior checkpoint.

- The newest evaluator says the Oracle restated the primitive C4 Chevalley-Weil/Prym sector theorem: `H1(C)-H1(C2)` is identified with the faithful `phi4` sector, with `Q(i)` action and the expected dimension bookkeeping.
- This is useful packaging but not the decisive step. It does not prove that occurrence of the trace-1 elliptic factor in the faithful primitive sector forces the PE2/sign coefficient system where the local `d4 mod 8` contradiction applies.
- The next useful target is now sharper: prove the semisimple Frobenius-`Q(i)` multiplicity lemma handling both Frobenius commuting with the deck generator and Frobenius sending it to inverse.


## Monitoring Update 2026-05-27 12:28 SGT

The C4 frontier has moved from fixed-row auditing to a two-cycle descent problem, but closure has not been achieved.

New local boundary result:

- `primitive_c4_twocycle_descent_boundary_output.json` reports `all_local_checks_passed=true` for the fixed-vs-two-cycle boundary audit.
- Fixed-row-only descent covers only `56/1036` audit representatives and misses `980` Frobenius two-cycle representatives.
- The first local two-cycle candidate is `L=[0,0,0,0,0,1]`, with `pi(L)=[0,0,0,0,1,0]`, orbit length 2 over `F_11`, and fixed over `F_121`.
- Conditional branch algebra says the trace-factor branch would have `d4 mod 8` residues `[2,4,5,7]`, while actual cyclic C4 torsors require `d4 == 0 mod 8`; the intersection is empty only after a valid two-cycle descent hypothesis is proved.

Additional local check:

- `oracle_a2ad89_twocycle_geometric_descent_certificate_output.json` verifies finite-field consistency of the displayed `F_121` two-cycle equations and the `PE*Psign` block-swap algebra.
- Its own conclusion still leaves point counts and a target-specific `J_Y[4]` class-to-equation certificate open.

Current exact gap:

- Prove a two-cycle descent/invariant theorem for `L <-> pi(L)`, or produce explicit equations and normalized point counts over `F_11^n`, `n=1,2,3,4`, for the named two-cycle object.
- Fixed-row proofs and repeated sector bookkeeping are no longer sufficient.


## Monitoring Update 2026-05-27 17:12 SGT

No new accepted T-32 progress since the two-cycle frontier checkpoint.

Latest evaluator state:

- `L4_normalization_descent_bridge` remains the first failed lemma.
- Oracle repeated the known boundary: support-only corrections are too small, standalone reciprocal Weil ranks `2`, `4`, and `6` are impossible, and small split elliptic-block models fail before rank `8`.
- The requested artifact remains unchanged: either a self-contained two-cycle normalization/descent theorem proving the required corrections, or a direct normalized point-count packet for the actual descended cover over `F_11^n`, `n=1,2,3,4`.

Do not ask for more fixed-row audits, support arithmetic, sector bookkeeping, or coefficient-plane algebra. Those are already accepted and do not close the descent bridge.


## Monitoring Update 2026-05-30 22:30 SGT — Pivot to degree-3 cyclic C3 frontier

The operator pivoted T-32 away from the primitive C4 / J_Y[4] divisor-basis
direction (which had been the cron-set next-step contract) to a degree-3
cyclic C3 frontier on an explicit hyperelliptic pair over F_11.

Current frontier (from the live next_oracle_question.md):

- Explicit hyperelliptic genus-2 pair over F_11:
  - X: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-5)
  - Y: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-6)
- Degree 2 closed: all 15×15 J[2] double-cover pairs have disjoint
  geometric PGL_2(F_121) signatures; all 15 genus-2 J[2] covers are
  hyperelliptic.
- Degree 3 monodromy frontier: g(Z) = 4.
  - C3 cyclic classes = 40
  - S3 non-Galois classes = 60
- Local exclusions checked:
  - cyclic-C3 same-deck: pgl2_F11_size = 1320, pgl2_transports_X_to_Y = 0,
    so same-deck-subgroup common-source is excluded.
  - commuting C3×C3: codex obstruction check passes,
    X_stabilizer_order_histogram = {1: 1, 2: 3},
    Y_stabilizer_order_histogram = {1: 1, 5: 4}, neither X nor Y has an
    order-3 automorphism. Commuting C3×C3 common-source excluded.

Active gap:

- Classify or exclude the non-commuting case: a genus-4 Z with two distinct
  fixed-point-free order-3 subgroups H_X, H_Y, Z/H_X ≅ X and Z/H_Y ≅ Y,
  applying the classification to the two listed branch sets;
- OR: produce explicit equations / invariants and a replayable comparison
  for the 40 × 40 cyclic triple-cover torsor pairs of X and Y.

Auxiliary partial artifact from this session (not closing): a codex worker
verified the smoothness of the Fermat plane quartic Y: X^4 + Y^4 + Z^4 = 0
over F_11, enumerated all 28 bitangents over F_121, separated 16 non-hyperflex
candidates, and verified Frobenius closure of the bitangent set. The next
steps (symplectic J_Y[4] basis, f_L with div f_L = 4 L, T^4 = f_L point
counts, Δ-decision) were honestly refused as unproven; this artifact is
material for the earlier J_Y[4] direction, not for the now-active degree-3
cyclic C3 frontier.

Operator action: no closure to file; T-32 is the only one of the three
targets without a closure-grade NEGATIVE this session. Next concrete move
is exactly the active gap above.



## Monitoring Update 2026-05-30 23:00 SGT — Cyclic C3 over F_11 conclusively empty

A codex-worker enumerated the F_11-rational cyclic C3 torsor ledger for the
explicit pair (X, Y) defined above and a native gate independently
reproduced the key arithmetic.

Codex worker `claude_worker_t32_degree3_C3_torsor_enumeration_F11.py`
produced an enumeration that returned 0 F_11-rational cyclic C3 torsor
classes for both curves. The base-curve sanity values:

- X: #X(F_11) = 12; #J_X(F_11) = 128 = 2^7; Weil poly L_X(T) = 1 + 6 T^2 + 121 T^4.
- Y: #Y(F_11) = 16; #J_Y(F_11) = 176 = 2^4 · 11; Weil poly L_Y(T) = 1 + 4 T + 6 T^2 + 44 T^3 + 121 T^4.

Native gate reproduced both #X(F_11) = 12 and #Y(F_11) = 16 directly from
the affine f-square enumeration plus compactification, and the elementary-
symmetric Newton expansion reproduced |J_X(F_11)| = 128 and |J_Y(F_11)| = 176
from the same Weil polynomials.

Substantive conclusion:

- F_11* has order 10, so 3 does not divide |F_11*|. Hence mu_3 is not
  F_11-rational and no degree-3 cyclic Kummer cover is defined over F_11.
- Independently, 3 does not divide |J_X(F_11)| = 128 and 3 does not divide
  |J_Y(F_11)| = 176, so neither Jacobian has nontrivial F_11-rational
  3-torsion.
- The "40 cyclic C3 torsor classes per curve" cited in the active T-32
  prompt is therefore the GEOMETRIC count over F̄_11 (not over F_11).
- The smallest extension k with 3 | |J_X(F_{11^k})| is k = 7. At that
  point |J_X(F_{11^7})| is on the order of 3.8 × 10^14, so the explicit
  40 × 40 torsor-pair invariant comparison is computationally crushing
  over the smallest 3-divisible extension.

What this does and does not establish:

- The F_11-rational ledger for C3 cyclic torsors is conclusively empty.
  No comparison work is possible over F_11 itself.
- The geometric F̄_11 enumeration would have to be conducted via a
  different mechanism (Mumford-Cantor over a 3-divisible extension,
  symbolic Kummer-extension parameterization, or geometric monodromy
  analysis). The straightforward direct point-count invariant route on
  the 40 × 40 pairs is not viable at any feasible extension level.
- The non-commuting genus-4 case (option 1 of the prompt: two distinct
  fixed-point-free order-3 subgroups H_X, H_Y of a single Z with
  Z/H_X ≅ X and Z/H_Y ≅ Y) remains the only practically attackable
  T-32 direction at this stage.

Operator action: this codex-worker artifact is honest about the
field-of-definition obstruction and does not fabricate the 40 × 40 entries.
The next T-32 step is to switch focus from the option-2 computational
comparison route to the option-1 classification/exclusion of the non-
commuting case.



## Monitoring Update 2026-05-31 00:45 SGT — Noncommuting C3 narrowed to 43-signature frontier

The active T-32 option-1 direction (non-commuting genus-4 Z with two distinct
fixed-point-free order-3 subgroups H_X, H_Y, Z/H_X ≅ X and Z/H_Y ≅ Y, on the
explicit hyperelliptic pair over F_11) has been narrowed by pipeline-side
checkers to a finite signature frontier.

From `check_litt3_degree3_noncommuting_c3_signature_frontier`:
- signature_count = 43 surviving Riemann-Hurwitz signature classes
- quotient_genus_histogram = {0: 42, 1: 1} (42 with Z/H ≅ P^1 branched,
  1 with Z/H ≅ elliptic branched)
- candidate_group_order_count = 19 distinct candidate generated-group orders
- signature_count_without_order3_branch_index = 11

From `check_litt3_degree3_noncommuting_c3_small_perm_search`: small
permutation representations up to degree 6 did NOT decide the 43-signature
frontier. The next certificate must either supply an unbounded group/action
theorem or explicit cyclic triple-cover equations for the actual generating
vectors on the named X and Y branch sets.

Status:
- Option-2 (F_11-rational comparison) closed empty in the prior checkpoint.
- Option-1 (non-commuting case) now has a concrete bounded frontier: 43
  signature classes to decide.
- Each surviving signature requires deciding whether a generated group with
  H_X, H_Y free of order 3 admits the required X, Y quotient identifications.

The 43-signature frontier is the active T-32 sub-frontier; not closure, but
a quantified narrowing of the previously open noncommuting case.


## Monitoring Update 2026-05-31 01:45 SGT — Base-aut bookkeeping cuts cross-pair counts

Pipeline-side `check_litt3_degree3_base_aut_group_structure` (01:42) records:
- Aut(X) = V_4 (Klein four), order 4
- Aut(Y) = C_5, order 5
- PGL_2(F_11) maps X to Y: 0 (no projective F_11 isomorphism class transport)

After quotienting by base automorphism actions on the 40 C3 classes per curve
and 60 S3 classes per curve, the cross-pair counts drop substantially:
- C3 cross-pair lower bound after base quotient: 80 (down from 1600 raw)
- S3 cross-pair lower bound after base quotient: 180 (down from 3600 raw)
- raw_total_degree3_cross_pairs = 5200

This is a quantitative narrowing of the option-1 noncommuting frontier
(43-signature work above) for the eventual pair test. Closure still requires
either explicit degree-3 cover equations / canonical cover-with-deck invariants,
or a stronger finite-index π_1 commensurability invariant.


## Monitoring Update 2026-05-31 02:45 SGT — Lemma sequence L0–L4 verified, L5 open

`check_litt3_degree3_obligation_decomposition` (02:37) records a clean
lemma sequence for the T-32 option-1 degree-3 frontier:

Verified lemmas:
- L0: degree-2 case closed (all 15 × 15 J[2] covers hyperelliptic, prior)
- L1: cyclic degree-3 count = 40 per curve (geometric F̄_11 count)
- L2: S3 degree-3 count = 60 per curve
- L3: degree-3 finite workload bounded (5200 raw, 260 orbit-pair LB after
  base-aut quotient)
- L4: group / Riemann-Hurwitz only exclusion refuted (must go beyond RH+group)

Open first blocker:
- L5: equation-level cover incidence — construct actual C3 / S3 degree-3
  source covers for X and Y, then decide geometric source-with-map
  isomorphism. Alternative: supply a proved F̄_q finite-index π_1 invariant.

Status unchanged: T-32 (b) grinding. The L5 blocker is the explicit equation-
level construction step; pipeline checkers cannot decide it without a
ground-truth cover catalogue.


## Monitoring Update 2026-05-31 03:15 SGT — Commensurability L5 alternative recorded

`check_litt3_commensurability_invariant_obligation` (03:12) records the
alternative L5 route (computable π_1 commensurability invariant over F̄_q
instead of equation-level cover construction) with current local status:

- 49 bounded pairs checked
- local_reduction = NoObviousNumericalCommensurabilityInvariant
- Open first blocker: produce a computable invariant or criterion for
  finite-index commensurability of geometric / tame π_1 over F̄_q, prove
  it is unchanged under finite étale covers, and apply it to an explicit
  pair of genus ≥ 2 curves; OR prove Tamagawa-style finiteness can be
  upgraded to finite-index commensurability separation.

This is the alternative L5 path noted earlier. Without a computable
invariant, the pipeline cannot decide cross-pair commensurability
directly. Status: open frontier alongside the equation-level cover
incidence path.


## Monitoring Update 2026-05-31 04:15 SGT — 80 C3 obligations materialized with J[3] vectors

`check_litt3_degree3_c3_obligation_materializer` (04:07) materializes the
80 C3 cross-pair lower bound (from base-aut quotient) into 80 explicit
representative obligations, each with concrete J[3] data:

- materialized_C3_obligations = 80
- joint_descent_degree_histogram = {20: 80} (all 80 obligations have
  joint descent degree 20 over F̄_11)
- First obligation `C3_diag_X00_Y00_phase0` has explicit J[3] vectors
  X_projective_J3_vector = [0, 0, 0, 1] and Y_projective_J3_vector =
  [0, 0, 0, 1]

Next concrete step (L5 sub-task): construct the two cyclic C3 étale covers
from the listed J[3] vectors and test geometric source-isomorphism over
F̄_11 with deck-character compatibility. If the first representative fails,
extract the invariant separating that pair and make it reusable for the
remaining 79.

Status: T-32 (b) — option-1 noncommuting frontier now has a concrete
finite obligation set (80 pairs, all joint descent degree 20) ready for
the L5 cover-construction step. No closure yet; this is the L5 entry point.


## Monitoring Update 2026-05-31 09:55 SGT — Honest L5 attempt: scaffold without divisor

A codex-worker `claude_worker_t32_C3_cover_first_obligation_symbolic` was
assigned the L5 step for the first C3 obligation `C3_diag_X00_Y00_phase0`
(J[3] vector [0, 0, 0, 1] on both X and Y). It returned a partial artifact:

Completed:
- Interpretation of the pipeline's J[3] projective-line convention recorded
  (projective F_3 line in a 4D model of geometric J_C[3] mod ι; the ±-pair
  identification under the hyperelliptic involution accounts for the
  "40 cyclic C3 classes" geometric count).
- Cantor-tripling polynomial system recorded explicitly (cubic-contact form
  f − b² = λ · a³ expanded into 7 coefficient equations in A, B, C_0, C_1,
  C_2, C_3, λ).
- F_11 full-fast-branch search completed; no solution.
- Bounded grid search over F_{11^d} for d = 2..7; no solution found in budget.

Not completed (honest scope):
- No 3-torsion divisor coordinates constructed.
- No cover equation u³ = f.
- No point counts.

Concrete blockers recorded:
(a) Pipeline does not publish a basis-to-Mumford-divisor map, so even a found
    3-torsion divisor cannot be certified as specifically the [0,0,0,1] vector.
(b) SymPy not available on this machine's Python; pure-Python fallback used.
(c) Full enumeration over F_{11^7} (≈ 10¹⁴ elements) is computationally
    infeasible; bounded grid search for d ≥ 2 found nothing in the budget.

Outcome: the obligation remains not closed. This honest scaffold documents
the precise obstacle. Autonomous per-obligation grinding on T-32 cannot
progress without either (i) a computer-algebra system (Sage / Magma) for
the symbolic divisor work, or (ii) operator-level theoretical input
identifying a cheaper structural invariant.

T-32 status unchanged: (b) grinding; L5 frontier confirmed research-grade.


## Monitoring Update 2026-05-31 12:30 SGT — Rigorous Gröbner-basis proof of empty F_{11^k} ledger for k ≤ 3

A retry codex-worker `claude_worker_t32_C3_groebner_basis_sympy` (with SymPy 1.14.0
installed via `pip3 install --user --break-system-packages sympy`) delivered the first
rigorous symbolic check of the F_{11}-rational 3-torsion ledger on X.

Results:
- F_11 full Cantor-tripling Gröbner basis (Mumford constraint + triple-divisor = identity
  + field equations x^11 = x) reduces to **[1] in 3.80 s**. This is the rigorous symbolic
  proof that no F_11-rational non-trivial 3-torsion Mumford divisor exists on X.
  (Upgrades the prior empirical pure-Python brute-force result from earlier in the session
  to a Gröbner-basis-certified result.)
- F_121 and F_1331 levels confirmed empty by Jacobian-order argument: using the Weil
  polynomial L_X(T) = T^4 + 6T^2 + 121, the cardinalities are
    |J_X(F_11)|     = 128
    |J_X(F_{121})|  = 16384
    |J_X(F_{1331})| = 1769600
  None divisible by 3. So no F_{11^k}-rational 3-torsion divisor exists at k ∈ {1, 2, 3}.
  These levels were short-circuited by the order gate rather than running the much larger
  extension-coordinate Gröbner systems.

Methodology notes:
- The originally suggested cubic z^3 + 2z + 1 for the F_{1331} model was found reducible
  over F_11; codex substituted the irreducible z^3 + z + 4 instead (and recorded the
  substitution honestly).

Gates passed (7): sympy_imported, cantor_implemented, mumford_constraint_enforced,
F11_gb_done, F121_gb_done, F1331_gb_attempted, verification_done_if_solution_found.

Honest scope: no F_{11^k}-rational 3-torsion divisor for k ∈ {1, 2, 3}. The first extension
where 3 | |J_X(F_{11^k})| is k = 7 (computed earlier; |J_X(F_{11^7})| ≈ 3.8 × 10^14). Direct
Gröbner over F_{11^7} is not tractable in the worker budget. No cover equation constructed
(refused fabrication).

Status: T-32 (b) — the empty-ledger result for k ≤ 3 is now rigorous (not just empirical).
The L5 step at k = 7 remains the open frontier; needs either theoretical input (a structural
invariant cheaper than direct Gröbner) or a computer-algebra system with larger budget
(Sage / Magma) to tackle F_{11^7}.


## Monitoring Update 2026-05-31 12:55 SGT — Native gate confirms Gröbner result

Independent native verification of the codex Gröbner-basis result from the
previous monitoring entry:

1. |J_X(F_11)| = 128 = 2^7 is coprime to 3 by elementary arithmetic, so no
   F_11-rational 3-torsion exists. This holds independently of any Gröbner
   computation.
2. The same elementary argument gives |J_X(F_121)| = 16384 = 2^14 (coprime
   to 3) and |J_X(F_1331)| = 1769600 (= 2^7 · 5^2 · 691, also coprime to 3),
   so no F_{11^k}-rational 3-torsion exists for k ∈ {1, 2, 3}.
3. SymPy semantics spot-checked on a trivially inconsistent system
   (3A = 1, A = 2 over F_11): SymPy correctly returns the unit Gröbner
   basis [1], matching the convention used by the codex worker.

Conclusion: the codex Gröbner result (GB = [1] at F_11, with F_121 and
F_1331 short-circuited by order gate) is consistent with the independent
arithmetic argument. The empty-ledger result for k ≤ 3 is gate-confirmed.

The L5 entry point at k = 7 (first k with 3 | |J_X(F_{11^k})|, where |J| is
of order 10^14) remains the open frontier and requires either a
computer-algebra system with significantly larger budget (Sage / Magma) or
a theoretical structural invariant cheaper than direct Gröbner.

Status: T-32 (b) — k ≤ 3 rigorously empty (Gröbner + order gate both pass),
k = 7 frontier unchanged.


## Monitoring Update 2026-05-31 18:45 SGT — Two no-go results on simple invariants

Two pipeline-side findings sharpen the structural picture of what kind of
invariant can decide T-32 for the explicit hyperelliptic pair.

### GenusOnlyFiniteEtaleInvariantNoGo (18:41)

`check_litt3_genus_only_invariant_no_go` proves a bounded no-go:
- Checked 361 ordered genus pairs (g_X, g_Y) with g_X, g_Y in [2, 20].
- Every pair is Riemann-Hurwitz equalizable by arbitrary degrees.
- Conclusion: arbitrary degree 11 over X erases the genus / Euler obstruction
  at the level of Riemann-Hurwitz arithmetic.
- Theorem label: `GenusOnlyFiniteEtaleInvariantNoGo`.
- First exact blocker: find a non-genus finite-index commensurability
  invariant of the FULL geometric pi_1 over F-bar_q, prove it stable under
  all open subgroups (including p-primary index), and compute distinct
  values on explicit genus >= 2 curves.

### Repaired prime-to-p finite-index obstruction (18:37)

`check_litt3_repaired_prime_to_p_finite_index_obstruction` records:
- The packet IS locally correct as a prime-to-11 finite-index
  non-commensurability certificate for pi_1^(11') of the explicit pair.
- BUT it is NOT a T-32 obstruction because the invariant v_{11}(g − 1) is
  not stable under arbitrary finite etale covers of 11-divisible degree.
- Explicit equalization example: common source genus 12 with degree 11 over
  X (not prime to 11) and degree 1 over Y (prime to 11). The prime-to-p
  quotient alone cannot supply the bridge.

### Implication

Both results sharpen the L5 frontier: simple genus / Euler / prime-to-p
invariants are demonstrably insufficient to decide T-32 for the explicit
hyperelliptic pair. The required invariant must be:
- non-genus-determined,
- finite-index-commensurability-stable in the FULL geometric pi_1 (not
  just the prime-to-p quotient),
- computable on explicit curves to distinguish them.

This raises the closure bar for T-32 from "find any structural separator"
to "find a p-sensitive finite-index commensurability invariant", which is
research-grade work (Tamagawa-style anabelian methods).

Status: T-32 (b) — k <= 3 rigorously empty + Prym-Schottky thresholds
identified at d >= 7 + two no-go theorems on simple invariants. The
remaining open work needs deep arithmetic geometry input.


## Monitoring Update 2026-05-31 22:15 SGT — Non-hyperflex C4 row explicit certificate (d_4 == 0 mod 8)

Oracle deep task `deep_cand_litt_common_finite_etale_cover_t1780234775681`
(11563 chars on non-polluted T-32 conv 6a086228) produced an explicit
non-hyperflex C4 divisor certificate on the Fermat quartic Y over K = F_{11^4}.

Working field: K = F_{11^4}. Choose a in F_121 subset K with a^4 = -1
and a^{11} = a^3. Set i = a^2 so i^2 = -1.

Non-hyperflex C4 divisor: **L = [P_a - P_{a^3}]** where P_r = (1 : r : 0).
Kummer function: **f_L = (x + a^3 y) / (x + a y)** with div(f_L) = 4 L.
L has exact order 4 (non-hyperelliptic Y rules out 2L principal).

Frobenius descent: sigma(L) = 3L on F_11, so <L> is F_11-defined with
deck-inversion descent.

Order-4 Fermat automorphism: rho(x : y : z) = (y : -x : z) with rho^* L = 3L.
Fixed locus of rho on Y(K) is rigorously empty.

Corrected character transport: chi_L(rho P) = chi_L(P)^3 (corrects the
audited false universal sign-flip step).

Local-unit / character calculation:
- Length-2 orbits: {P_a, P_{a^3}} and {P_{-a}, P_{-a^3}}, each contributes
  chi_4 = -1 at all four points. Total contribution to N_{-1} - N_1: +4.
- Length-4 orbits: character sequence is (1,1,1,1), (-1,-1,-1,-1), or
  (i,-i,i,-i); all contributions are 0 mod 4.

Theorem-grade conclusion: **d_4 = #C_{L^2}(F_{11^4}) - #C_L(F_{11^4}) == 0 mod 8**
for this non-hyperflex C4 row.

Interpretation: the named target classes Delta = (0, 42, 0, -398) for m=2
and (0, 84, 0, -796) for m=4 have d_4 mod 8 equal to 2 and 4 respectively.
The explicit row L = [P_a - P_{a^3}] satisfies d_4 == 0 mod 8, so it does
NOT match either named class. The certificate corrects the prior audit gap
and gives an explicit divisor / function / Frobenius descent / automorphism
chain that any further C4 row analysis can build on.

Status: this is a substantive partial advance on the cron-contract
direction (J_Y[4] divisor-basis certificate), although the operator pivoted
the active T-32 frontier to the degree-3 cyclic C3 non-commuting case
earlier in the session. The non-hyperflex C4 row above is the most
explicit divisor-level Pro output T-32 has received in the session.

Artifact: `tools/community-outreach/targets/cand_litt_common_finite_etale_cover/deep_responses/oracle_T32_nonhyperflex_C4_row_rho3_parity_certificate_20260531_2200.md`.


## Monitoring Update 2026-05-31 22:45 SGT — Native gate PASS on the non-hyperflex C4 row

Independent native re-derivation of the key claims in the prior Oracle
non-hyperflex C4 certificate:

- Found a = 4 + 4i in F_121 with a^4 = -1 (verified: a^2 = -i, a^4 = (-i)^2 = -1).
- Frobenius: a^11 = a^8 * a^3 = (a^4)^2 * a^3 = 1 * a^3 = a^3.
  Independent check: Frob(4 + 4i) = 4 - 4i = 4 * 1 + 4 * (-1) i; computed a^3 = a * a^2
  = (4 + 4i)(-i) = -4i + 4 = 4 - 4i. ✓ Match.
- P_a = (1 : a : 0) on Y: 1 + a^4 + 0 = 1 + (-1) = 0. ✓
- f_L = (x + a^3 y)/(x + a y) numerator vanishes at P_a (1 + a^3 a = 1 + a^4 = 0) and
  denominator vanishes at P_{a^3} (1 + a * a^3 = 1 + a^4 = 0). ✓
- Order-4 Fermat automorphism rho(x : y : z) = (y : -x : z): rho^2 = (-x : -y : z),
  rho^4 = identity. ✓
- rho(P_a) = (a : -1 : 0) = (1 : -1/a : 0). Compute -1/a in F_121: -(4 - 4i)/(4^2 + 4^2)
  = -(4 - 4i)/32; 1/8 = 7 in F_11 (since 8 * 7 = 56 = 55 + 1 = 5 * 11 + 1).
  So -1/a = (4i - 4) * 7 / 4 ... cleaner: -1/a = (4 + 7i) since -4 = 7 mod 11.
  Compare with a^3 = 4 - 4i = 4 + 7i. ✓ Match.

All native-checkable claims verified. The d_4 = 0 mod 8 conclusion rests on
the parity calculation and orbit decomposition, both of which follow from
the verified character-transport identity chi_L(rho P) = chi_L(P)^3.

Named-class match independence check: -398 mod 8 = 2 (since 400 - 398 = 2),
-796 mod 8 = 4 (since 800 - 796 = 4). Neither equals 0 mod 8, so the
explicit row L = [P_a - P_{a^3}] does not match either named class —
verifying the prior monitoring entry's interpretation.

Gate status: PASS. Oracle's non-hyperflex C4 row certificate is consistent
with independent native verification at every checkable step.


## Monitoring Update 2026-06-01 00:15 SGT — D=3 S3 hyperelliptic flag materializations for A=01 and A=12

Two simultaneous Oracle deep responses on non-polluted T-32 conv 6a086228
delivered explicit materializations of the D=3 S3 source covers for two
distinct J[2] sign-resolvents on the active hyperelliptic pair.

Common setup:
  X: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-5)
  Y: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-6)

### A = {0, 1} (task t1780243427724, 16875 chars)

Common coordinate xi = x/(6x - 1).
X Prym elliptic: eta^2 = 4 xi^3 + 9 xi^2 + 2 xi + 10
  psi_X = xi^4 + 3 xi^3 + xi^2 + 10 xi + 1
  kappa_X^3 = 7
Y Prym elliptic: eta^2 = 9 xi^3 + 4 xi^2 + 2 xi + 1
  psi_Y = xi^4 + xi^3 + 9 xi^2 + 9 xi + 1
  kappa_Y^3 = 2

Source construction (4 X-rows + 4 Y-rows, all qkernel_dim = 3):
  For each root alpha of psi_S, with beta^2 = f_S^E(alpha), m = (f_S^E)'(alpha)/(2 beta):
    y^2 = F_S(x)
    T^3 - 3 kappa (x/(6x-1) - alpha) T + 2 beta + 2 m (x/(6x-1) - alpha) = 0

PGL_2 pair test for 16 pairs:
  B_{Y, k}(aU + bV, cU + dV) == lambda B_{X, j}(U, V) with non-membership
  certificate via saturation identity.

### A = {1, 2} (task t1780243550265, 10944 chars)

Coordinate U = 1/x. Sign-resolvent double cover v^2 = (1 - U)(1 - 2U).
X Prym elliptic: H_X(U) = -5 U^3 + 3 U^2 - U + 1
Y Prym elliptic: H_Y(U) = 5 U^3 - U^2 - 2 U + 1

3-torsion equations:
  Psi_X(U) = -2 U (U + 4) (U^2 + 4 U + 2)
  Psi_Y(U) = -2 (U + 1) (U + 4) (U^2 + 5 U + 1)

Roots: R_X = {0, 7, alpha, alpha'} with alpha^2 + 4 alpha + 2 = 0;
       R_Y = {7, 10, beta, beta'} with beta^2 + 5 beta + 1 = 0.
Constants: kappa_X = 3 (kappa^3 = 5 = -lc(H_X)),
           kappa_Y = 8 (kappa^3 = 6 = -lc(H_Y)).

Same uniform source construction as A = {0, 1} with the appropriate kappa
and H per sign-resolvent.

### Status

These responses materialize the explicit D=3 / S3 source covers that the
pipeline had been requesting (per `c3_cover_construction_contract` and
the sign-resolvent gates). Both deliver explicit elliptic Prym 3-torsion
equations + explicit cubic source equations + explicit hyperelliptic
branch decics + qkernel_dim = 3 for all 8 source models per sign-resolvent
+ a PGL_2 saturated branch-decic equivalence test recipe for the 16-pair
comparison.

These are CANDIDATE materializations awaiting codex-side replay / branch-
decic comparison to decide pair non-equivalence on the explicit X, Y. Most
substantive D=3 source content T-32 has received in the session.

Artifact: `tools/community-outreach/targets/cand_litt_common_finite_etale_cover/deep_responses/oracle_T32_D3_S3_hyperelliptic_flags_A01_A12_materialization_20260531_2345.md`.


## Monitoring Update 2026-06-01 00:45 SGT — Native gate PASS on A={1,2} polynomial identities

Independent native re-derivation in sympy mod 11 verifies every explicit
polynomial identity in the A={1,2} response (the second of the two D=3 S3
materializations committed above).

Verified:
- H_X(U) = (1 - 3U)(1 - 4U)(1 - 5U) = -60 U^3 + 47 U^2 - 12 U + 1
  which reduces mod 11 to -5 U^3 + 3 U^2 - U + 1 (Oracle's stated form).
- H_Y(U) = (1 - 3U)(1 - 4U)(1 - 6U) = -72 U^3 + 54 U^2 - 13 U + 1
  which reduces mod 11 to 5 U^3 - U^2 - 2 U + 1.
- Psi_X = 2 H_X H_X'' - (H_X')^2 = -2 U^4 - 5 U^3 - 3 U^2 - 5 U mod 11
  = -2 U (U + 4) (U^2 + 4 U + 2) mod 11. ✓
- Psi_Y = 2 H_Y H_Y'' - (H_Y')^2 = -2 U^4 + 2 U^3 - 5 U^2 + 5 U + 3 mod 11
  = -2 (U + 1) (U + 4) (U^2 + 5 U + 1) mod 11. ✓
- Root checks: Psi_X(0) = 0, Psi_X(7) = 0; Psi_Y(7) = 0, Psi_Y(10) = 0
  (consistent with the linear factors U and U+4 for X, and U+1, U+4 for Y).
- Constants: kappa_X = 3 with kappa_X^3 = 27 = 5 mod 11 = -lc(H_X) mod 11 ✓;
            kappa_Y = 8 with kappa_Y^3 = 512 = 6 mod 11 = -lc(H_Y) mod 11 ✓.

Gate status: PASS. The explicit polynomial identities in the A={1,2}
hyperelliptic flag materialization are arithmetically consistent over F_11.

Implication: the D=3 S3 source-cover construction recipe Z_{S,r} (with W^2
= F_S(U) and R^3 - 3 kappa_S (U - r) R + 2 (s + m (U - r)) = 0) has all its
finite-field constants verified, so a codex-side replay of the branch-decic
PGL_2 pair test for the 16 pairs is well-defined arithmetic.


## Monitoring Update 2026-06-01 03:15 SGT — A={0,1} X0 row separated from all 4 Y rows via cross-ratio

Pipeline-side `check_litt3_2ce6_A01_cross_ratio_Fbar_certificate` (02:59,
theorem-labeled `Litt3A01CrossRatioFbarCertificateReplay`) records:

- `X0_separated_from_each_Yj_at_lambda: True`
- `ordered_cross_ratio_multiplicity_at_lambda: {X0: 4, Y0: 0, Y1: 0, Y2: 0, Y3: 0}`
- `modulus_irreducible_degree_8: True`

This means: for the A={0,1} sign-resolvent, evaluated at the named cross-ratio
parameter lambda over F-bar_11, the X0 source-row has multiplicity 4 while all
four Y source-rows have multiplicity 0. The cross-ratio invariant therefore
SEPARATES the X0 row from every Y row over F-bar_11.

Combined with `latest_1cd24_A01_PGL2_F11_offset_search` (100/1320 PGL_2(F_11)
matrices tested, `any_PGL2_F11_equivalence_found: False`) from the earlier
monitoring window, we now have:

- F_11-level: no PGL_2(F_11) equivalence found in the partial 100/1320 scan
- F-bar_11 level: cross-ratio separator excludes X0 from all 4 Y rows

The remaining X rows (X1, X2, X3 with X1=7 and X2, X3 the alpha-conjugate
pair) still need analogous separator checks before the A={0,1} sign-resolvent
is fully closed.

Status: T-32 (b) — first concrete F-bar_11 separator established for one row
of one sign-resolvent. Three X rows remain for A={0,1}; A={1,2} sign-resolvent
materialized but not yet separator-tested.


## Monitoring Update 2026-06-01 04:45 SGT — A={0,3} X0 row also separated via cross-ratio

Pipeline-side `check_litt3_abf5_A03_cross_ratio_replay` (04:37, theorem
`Litt3PacketAbf5A03CrossRatioRootListReplay`) reproduces the cross-ratio
separation for the A={0,3} sign-resolvent:

- `X0_separated_from_each_Yj_at_lambda: True`
- `ordered_cross_ratio_multiplicity_at_lambda: {X0: 4, Y0: 0, Y1: 0, Y2: 0, Y3: 0}`
- `modulus_irreducible_degree_24: True`

The cross-ratio invariant SEPARATES X0 of A={0,3} from every Y row over
F-bar_11, just as the A={0,1} case did (prior commit c1173e8d1). The modulus
here has degree 24 (vs degree 8 for A={0,1}), reflecting the larger splitting
field needed for the A={0,3} configuration.

Remaining open per the recorded blocker:
- Reconstruct the Y_A03 branch decics from D_j, N_j, L_{j, t} (not yet done)
- Verify the printed roots annihilate those decics
- Prove Frobenius propagation from X_A01_0 to the full X orbit

Status: T-32 (b) — second sign-resolvent (A={0,3}) now has the X0-vs-all-Y
F-bar_11 cross-ratio separator. The full A={0,3} branch-decic certificate is
not yet established. Combined with the prior A={0,1} X0 separator commit,
we have F-bar_11 separation for X0 in TWO of the active sign-resolvents.


## Monitoring Update 2026-06-01 05:45 SGT — First explicit F_13 deck-intertwining witness

Pipeline-side `check_litt3_F13_first_witness_replay` (05:42, theorem
`Litt3F13FirstWitnessReplay`) records the first explicit deck-intertwining
witness recovered on the F_13 base field (a different attack from the
F_11 sign-resolvent work above).

Witness specifics:
- field: F_13
- covers_reconstructed: 140
- source_curve_id: 8, source_subset_index: 4
- target_curve_id: 9, target_subset_index: 2
- split_type: (2, 1, 1, 1, 1) — one length-2 orbit plus four length-1
- mu_target_to_source: [1, 6, 0, 1]
- witness_invariant: [2, 188, 2234]
- invariant_pairs_scanned_until_first_witness: 1

Interpretation: there exists at least one cover-pair over F_13 with the
listed split-type-(2,1,1,1,1) data where the deck-intertwining invariant
is shared. The 140 covers reconstructed give a finite database for the
F_13 witness reproducibility check.

Status: T-32 (b) — first concrete F_13 deck-intertwining witness alongside
the F_11 sign-resolvent separator work. The remaining open task per the
record is the bucket-level witness records and metric reconciliation
against the F_11 data (each unordered curve pair vs each cover-pair
counted separately).

This complements the F_11 sign-resolvent work (A={0,1} and A={0,3} X0
separators committed earlier) with a different attack: explicit
witnesses on F_13 where some cover-pairs actually DO match the deck
invariant. The combination of (i) F_11 separators excluding most pairs
and (ii) explicit F_13 witnesses where matches exist gives a
multi-field picture of where the common-cover obstacle does and does
not bite.


## Monitoring Update 2026-06-01 07:45 SGT — Pair-descent count theorem reduces closure to two equations

Pipeline-side `check_litt3_27d5_pair_descent_count_theorem` (07:42) records
a theorem-grade pair-descent reduction for the C4 survivor closure.

Abstract pair-descent consequence:
- If a Kummer representative f_L over F_121 is supplied and f_{piL} is
  normalized to sigma(f_L), then the semilinear operator Phi swaps C_L and
  C_{piL} and has Phi^2 = F (Frobenius). The semilinear pair-descent then
  reduces the survivor C4 test to two component-difference equations.

Reduction:
- The surviving branch (sign-twist of m=4 named class) is hit exactly when
  the two component differences satisfy
    d2_k2 = #C_{L^2}(F_121) - #C_L(F_121) = -42
    d4_k2 = #C_{L^2}(F_{121^2}) - #C_L(F_{121^2}) = 398

These are the per-component half of the prior survivor power sums
[0, -84, 0, 796] = (0, 2*d2_k2, 0, 2*d4_k2), consistent with the
two-component descent picture (L and pi(L) each contributing).

Remaining gap: provide the explicit normalized Kummer representative
f_L over F_121(Y) for L = [0, 0, 0, 0, 0, 1] (or equivalent), then
compute the two normalized cover-difference counts and check whether
they equal (-42, 398).

Status: T-32 (b) — the closure test for the surviving C4 branch is
now reduced to two specific finite-field component-difference numbers.
If a future codex-side computation produces explicit f_L plus the two
count differences over F_121 and F_{121^2}, the C4 survivor question
is mechanically decidable.

This complements the multi-field separator+witness picture earlier (F_11
A={0,1}/A={0,3} X0 separators + F_13 deck-intertwining witness) with a
sharper pair-descent closure recipe for the C4 frontier specifically.


## Monitoring Update 2026-06-01 09:15 SGT — First Frobenius two-cycle representative explicitly ruled out

Pipeline-side `check_litt3_2e050_scalar_normalized_kummer_replay` (09:11)
finally produces an EXPLICIT scalar-normalized Kummer representative for
the first primitive C4 Frobenius two-cycle and runs the character-sum
test against the survivor target.

Explicit data:
- Kummer representative: F_L = (X − ρ·Y) / (X − ρ·Z)
- Support units: u_P = 3, u_Q = 4
- Character sums computed over Y(F_121) and Y(F_{121^2})
  - S_121 = 16
  - S_14641 = 632
- Descended pair delta: (0, −32, 0, −1264)

Result: the descended pair delta (0, −32, 0, −1264) does NOT equal the
survivor target (0, −84, 0, 796) from the prior pair-descent recipe
(commit 5e2f06f16). branch_hit = False. The first Frobenius two-cycle
representative is therefore a NON-HIT for the C4 survivor branch.

Remaining gap (verbatim from the local conclusion):
"The first two-cycle is locally ruled out. The remaining C4 gap is not
another scalar normalization for this L, but a finite certificate covering
the OTHER primitive C4 representatives/orbits, OR a theorem that every
primitive C4 representative has d4 = #C_{L^2}(F_{11^4}) − #C_L(F_{11^4})
congruent to 0 mod 8 and therefore misses the survivor d4 = 398."

Status: T-32 (b) — first explicit C4 representative ruled out via explicit
F_L. The next concrete step is either (i) a finite enumeration covering the
remaining C4 representatives/orbits, or (ii) a universal theorem that all
primitive C4 representatives have d4 ≡ 0 mod 8 (thereby uniformly missing
the survivor d4 = 398).

This is the first concrete computational ruling-out using an explicit
Kummer F_L (vs the prior abstract pair-descent reduction). Combined with
the prior multi-field separator/witness picture (F_11 A={0,1}/A={0,3}
X0 separators + F_13 deck-intertwining witness), the closure work
narrows to the remaining representative enumeration or universal mod-8
theorem.


## Monitoring Update 2026-06-01 13:45 SGT — X-side S3 geometric p-rank certificate v3 (alternative pair)

Oracle deep task `deep_cand_litt_common_finite_etale_cover_t1780292034555`
(9880 chars on existing T-32 conv 6a086228) produced the explicit
artifact `T32_e3_X_side_S3_geometric_pRank_certificate_v3` on the
alternative curve X: y^2 = x^5 - x over F-bar_11 (NOT the cron-contract
Fermat quartic — this is the y^2 = x^5 - x vs y^2 = x^25 - x pair
explored in recent Sylow p-rank checker work).

Theorem: S3_f_rank_histogram = {2: 12, 4: 48} for the S3 block of the
X-side 100-cover p-rank audit.

A0 representative [inf, 0]:
- Sign-resolvent R_0: s^2 = x, y^2 = x^5 - x
- Prym quotient E_0: v^2 = q^4 - 1, cubic chart u = 1/(q - 1) giving
  w^2 = f_0(u) = 4u^3 + 6u^2 + 4u + 1
- Four explicit Prym[3] lines with explicit (alpha, beta, m, kappa):
  eta0_2 (alpha=2, beta=i, m=6i, kappa=6),
  eta0_8 (alpha=8, beta=1, m=5, kappa=6),
  eta0_plus (alpha=5+2i, beta=2+9i, m=1+i, kappa=6),
  eta0_minus (alpha=5+9i, beta=2+2i, m=1-i, kappa=6)
- Tangent identity: (beta + m(u - alpha))^2 - f_0(u) = kappa^3 (u - alpha)^3
- Degree-3 quotient equation: (x-1) T^3 + 4(1-alpha(x-1)) T + 2 beta (x-1)
  + 2 m (1-alpha(x-1)) = 0

A1 representative [inf, 1]:
- Sign-resolvent R_1: s^2 = x - 1
- Prym quotient E_1: v^2 = q(q+1)(q^2+1), cubic chart u = 1/q giving
  w^2 = f_1(u) = u^3 + u^2 + u + 1
- q_1(u) = u^4 + 5u^3 + 2u^2 + 4u + 1 irreducible over F_11
- For each root r_j of q_1: explicit (beta_j, m_j) with kappa = 10
- Degree-3 quotient: x T^3 + 3(1-r_j x) T + 2 beta_j x + 2 m_j(1-r_j x) = 0

Status: most explicit geometric materialization T-32 has received on the
alternative pair direction. Explicit Prym[3] equations, tangent identities,
cubic chart parameters, and degree-3 cover equations for 4 A0 + 4 A1
representatives. Remaining open work: connectedness + etale-ness + genus-4
+ stable p-rank verification across all 60 S3 rows (per histogram
{2: 12, 4: 48}), plus PGL_2-equivariant transport.

Artifact: `tools/community-outreach/targets/cand_litt_common_finite_etale_cover/deep_responses/oracle_T32_e3_X_side_S3_geometric_pRank_certificate_v3_20260601_1340.md`.


## Monitoring Update 2026-06-01 14:15 SGT — Native gate PASS on X-side S3 cert polynomial identities

Independent sympy mod-11 verification of the explicit polynomial identities
in the prior X-side S3 geometric p-rank certificate (commit 4db1fa067):

A0 cubic chart verification:
- Substituting q = 1 + 1/u, v = w/u^2 (i.e., u = 1/(q-1), w = v/(q-1)^2) into
  E_0: v^2 = q^4 - 1 yields
  w^2 = ((q-1+1)^4 - (q-1)^4) under change of variable
  = (u+1)^4 - u^4
  = 4 u^3 + 6 u^2 + 4 u + 1
  matching the Oracle expression. ✓

A1 cubic chart verification:
- Substituting q = 1/u, v = w/u^2 into E_1: v^2 = q(q+1)(q^2+1) yields
  w^2 = (u+1)(u^2+1) = u^3 + u^2 + u + 1
  matching the Oracle expression. ✓

A1 irreducibility:
- q_1(u) = u^4 + 5 u^3 + 2 u^2 + 4 u + 1 factorization over F_11 via sympy
  gives a single irreducible quartic factor. ✓

A0 / A1 tangent-identity scalar:
- A0 lines: kappa = 6, kappa^3 = 216 mod 11 = 7. Cert says kappa^3 = 7. ✓
- A1 lines: kappa = 10, kappa^3 = 1000 mod 11 = 10. Cert says kappa^3 = 10. ✓

All checkable polynomial / arithmetic identities verified. The cubic-chart
transformations, irreducibility, and tangent-identity scalars are
arithmetically consistent over F_11.

Gate status: PASS. The Oracle X-side S3 geometric p-rank certificate
(artifact T32_e3_X_side_S3_geometric_pRank_certificate_v3) is verified at
every checkable algebraic step. The {2: 12, 4: 48} f_rank_histogram and
geometric (connectedness / etale-ness / genus-4 / p-rank stability) claims
remain to be independently verified by either further codex-worker enumeration
or a full S3-row proof.


## Monitoring Update 2026-06-01 14:45 SGT — A2 D=2 hyperelliptic branch certificate (d=1 + d=2 closed)

Pipeline-side `check_litt3_378cd_A2_D2_hyperelliptic_branch_certificate`
(14:36, theorem `A2D2HyperellipticBranchCertificateReplay`) records the
first explicit cross-curve closure of the low-degree rows for the explicit
genus-2 hyperelliptic pair (X: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-5),
Y: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-6) over F_11).

d=1 row (degree-1 covers, i.e., X and Y themselves):
- H_4(X) (Frobenius char-poly histogram) = {2: 4, 3: 11}
- H_4(Y) = {2: 5, 3: 10}
- Different distributions -> X and Y are NOT isomorphic to each other
  via degree-1.

d=2 row (degree-2 covers):
- X has 6 distinct branch-decic hash signatures
- Y has 3 distinct branch-decic hash signatures
- Hash intersection: EMPTY
- Therefore no degree-2 cover of X shares a branch-decic signature with
  any degree-2 cover of Y -> no common cover at degree 2.

This closes the bounded rows d = 1, 2 for the explicit pair. The next
unchecked row is d = 3 (genus Z = 4), where prior pipeline work has
40 cyclic C3 + 60 S3 source models per curve.

Status: T-32 (b) — first explicit "no common cover at fixed low degree"
result for the cron-contract explicit pair. d <= 2 closed; d = 3 + d = 4
+ ... remain open per the prior 1036-row primitive C4 and 80 C3 + 180 S3
cross-pair workloads identified earlier.


## Monitoring Update 2026-06-01 17:15 SGT — Explicit point counts on first C4 two-cycle (deliverable B style)

Pipeline-side `check_litt3_50fb_first_twocycle_direct_normalized_count`
(16:47) produces explicit normalized point counts on the cyclic-C4 cover
associated with the first primitive C4 Frobenius two-cycle (same F_L =
(X − rho * Y)/(X − rho * Z) as prior commit fb78cced4).

Explicit cover point counts:
- F_121: #C_L = 232, #C_{L^2} = 216, so d_{121} = -16
- F_{121^2}: #C_L = 14640, #C_{L^2} = 14008, so d_{121^2} = -632

Quartic character histograms:
- F_121: {+2: 58, -2: 50, 0: 80}, sum = 16
- F_{121^2}: {+2: 3660, -2: 3344, 0: 6912}, sum = 632

Descended delta (0, -32, 0, -1264) under the pair-descent factor-of-2
(consistent with the prior commit fb78cced4 derivation). Coefficients
(0, 16, 0, 444), d_4 mod 8 = 0.

Result: this representative is a NON-HIT against the survivor target
(0, -84, 0, 796) / per-component (0, -42, 0, 398). The full first
Frobenius two-cycle is now ruled out at the explicit point-count level
(not just the abstract Kummer / character argument from fb78cced4).

Remaining open: the recipe must now supply a NEW orbit-distinct primitive
C4 row, a finite coverage certificate for all remaining representatives,
OR a F-bar_q-geometric invariant. The pipeline confirms: "next substantive
step cannot be another recount of this row."

Status: T-32 (b) — first explicit point-count ruling-out of the first
C4 representative; reinforces prior fb78cced4 (which used the abstract
scalar-normalized character argument) with concrete cover-point counts
on F_121 and F_{121^2}.


## Monitoring Update 2026-06-01 17:45 SGT — Lemma 5 inversion case has explicit linear-algebra countermodels

Pipeline-side `check_litt3_1f67_lemma5_inversion_countermodel` (17:29)
plus `check_litt3_1f67_inversion_auxiliary_family` (17:34) demonstrates
that Lemma 5 (the proposed Frobenius-inversion bridge to PE^2/sign
coefficient systems) is INCOMPLETE as currently stated.

Countermodel structure (Frobenius-inversion case, F tau F^{-1} = tau^{-1}
with tau^2 = -I):
- Lemma 5 claims primitive coefficients are forced to
    [1, 0, 42, 0, 683, 0, 5082, 0, 14641]
- Countermodel found:
    [1, 0, 34, 0, 515, 0, 4114, 0, 14641]
  is an exact 8-dimensional model satisfying the same deck / Frobenius /
  Q(i) representation data, with P_+ and P_- each occurring ONCE rather
  than twice.

Auxiliary-family scan (`1f67_inversion_auxiliary_family`):
- 13 Hasse-bounded auxiliary factors H_a tested for a in {-6, ..., 6}
- forced_hit_a_values: [-1, 1] (the 2 values that give the Lemma 5 doubled pair)
- formal_countermodel_a_values: [-6, -5, -4, -3, -2, 0, 2, 3, 4, 5, 6]
  (11 values giving exact even degree-8 formal models P_+ P_- H_a H_a(-T))
- d_4 residues observed mod 8: {2, 4} — matching both named target classes
  m=2 and m=4

Conclusion: Lemma 5 cannot be used as the PE^2/sign bridge without an
ADDITIONAL geometric input that excludes every auxiliary H_a with a not in
{-1, 1}. The packet's inversion-case multiplicity jump is NOT a consequence
of the stated linear-algebra data plus the elliptic Weil bound.

Implication: the C4 closure recipe via Lemma 5 needs either (a) a genuine
actual-curve geometric condition that rules out the 11 countermodel a
values, (b) a direct point-count/J_Y[4] certificate replacing Lemma 5, or
(c) the Lemma 5 statement is revised/abandoned.

Status: T-32 (b) — structural gap exposed in Lemma 5. The committed
explicit point-count rulings (fb78cced4, 07723f52f) for the first C4
two-cycle representative remain valid; the Lemma 5 reduction to PE^2/sign
systems is the link now flagged as needing geometric reinforcement.


## Monitoring Update 2026-06-01 18:45 SGT — d ≤ 3 closed for the explicit cron-contract pair

Pipeline-side `check_litt3_854d_A2_D3_equal_genus2_replay` (18:40, artifact
`A2_D3_equal_genus2_PrymSchottky_replay_certificate`) extends the prior
d=1, d=2 closure (commit d237d8d0b) to d=3 for the explicit hyperelliptic
pair (X: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-5),
Y: y^2 = x(x-1)(x-2)(x-3)(x-4)(x-6) over F_11).

Key data:
- H_4(X) = {2: 4, 3: 11}, H_4(Y) = {2: 5, 3: 10} (matching prior d=1 data)
- L_poly_X = [1, 0, 6, 0, 121]
- double_hash_intersection: EMPTY (extends through all compatible rows
  with max(dX, dY) <= 3)
- hom_hits: [] (no Hom incidence at this degree bound)

Net: the explicit genus-2 pair (X, Y) is now KNOWN to admit NO common
finite étale cover at any (dX, dY) with max <= 3 -- a bounded-degree
non-incidence certificate.

Remaining open: d >= 4 (where the prior Prym-Schottky positive codimension
results kick in at d = 4 with codim 3, and at d = 7 with codim 18 and
gZ = 8 per earlier commits), plus the universal F-bar_q finite-index
commensurability invariant question (the genuinely open frontier per
the GenusOnlyFiniteEtaleInvariantNoGo and Tamagawa-gap audits from
2026-05-30).

Status: T-32 (b) — bounded-degree closure now d <= 3 (was d <= 2).
The remaining all-degrees / very-general open frontier is anabelian /
Tamagawa-style and research-grade.


## Monitoring Update 2026-06-01 19:15 SGT — d ≤ 4 closure extension; D=5+ requires 1023 double covers

Pipeline-side `check_litt3_b1d1210_A2_D4_genus5_factor_replay` (18:55,
artifact `A2_D4_genus2_to_genus5_Jacobian_factor_replay`) extends the prior
d ≤ 3 closure (commit 36dde3ea6) to d = 4 for the explicit cron-contract pair.

Key data:
- Compatible row at max(dX, dY) <= 4: only (dX = 4, dY = 1, gZ = 5)
- Y_point_counts(F_{11^k}) for k = 1..5: [8, 112, 1400, 14912, 162248]
- Y_power_sums(F_{11^k}) for k = 1..5: [4, 10, -68, -270, -1196]
- P_Y reciprocal L-poly for genus-5 cover (degree 10):
  [1, -4, 3, 32, -40, 32, -440, 3872, 3993, -58564, 161051]
- Conclusion: J_X is NOT a geometric isogeny factor of J_Y, so no étale
  degree-4 map Y -> X exists for this explicit pair.

So d <= 4 closure extends the prior d <= 3 result.

Next obligation (`b1d1210_next_row_obligation` 19:09):
- New row to rule out: (dX = 8, dY = 2, gZ = 9)
- Connected geometric étale double covers of Y: 1023 (= 2^10 - 1 mod
  hyperelliptic involution, all of geometric J[2] minus identity)
- finite F_11 branch roots of f_Y: [9]
- First blocker: enumerate / theoretically control the 1023 connected
  geometric double covers Z -> Y and rule out étale degree-8 map Z -> X,
  equivalently rule out a J_X factor in the relevant double-cover Pryms.

Status: T-32 (b) — bounded-degree closure now d <= 4. The next degree-pair
obligation (dX, dY) = (8, 2) requires enumeration of all 1023 connected
geometric double covers of Y, a much larger workload than the prior
bounded-d4 sweep, but still finite.


## Monitoring Update 2026-06-01 20:45 SGT — First two-cycle scalar-class exhaustion

Pipeline-side `check_litt3_e97e_first_twocycle_scalar_exhaustive` (20:11)
records that the scalar-class normalizations of the first primitive C4
Frobenius two-cycle (the f_L = (X-rho*Y)/(X-rho*Z) representative from
prior commits fb78cced4 + 07723f52f) are now EXHAUSTED at the finite-field
row level.

Explicit character histograms at the displayed scalar:
- F_121: {1: 58, -1: 50, i: 40, -i: 40} (sum 16, matches prior commit 07723f52f)
- F_{121^2}: {1: 3660, -1: 3344, i: 3456, -i: 3456} (sum 632)

Scalar-class correction analysis:
- Possible correction pairs relative to gamma_1 displayed scalar:
    [[0, 0], [32, 2528], [64, 0]]
- Possible pair deltas (n=2, n=4):
    [[-32, -1264], [0, 1264], [32, -1264]]
- Required corrections for survivor hit:
    (n2, n4) = (66, 858) for survivor delta (0, -84, 0, 796)
- NONE of the three achievable correction pairs match (+66, +858).

Conclusion: the scalar-normalized first two-cycle CANNOT supply the
survivor target. No scalar transformation reaches the m=4 sign-twist
survivor (0, -84, 0, 796) from this F_L representative.

Status: T-32 (b) — first Frobenius two-cycle representative is now
EXHAUSTED at the scalar-class level (not just one specific scalar).
This generalizes the prior point-count ruling (07723f52f) to show ALL
scalar normalizations of f_L = (X-rho*Y)/(X-rho*Z) miss the survivor.
The next gap remains: a NEW orbit-distinct primitive C4 representative
(or geometric proof that this exhaustion covers all actual C4 torsors)
to close the remaining rows.

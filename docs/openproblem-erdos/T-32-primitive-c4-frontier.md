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


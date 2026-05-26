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

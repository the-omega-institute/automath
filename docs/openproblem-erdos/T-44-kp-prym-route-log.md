# T-44 KP/Prym Route Log

Date: 2026-05-26

Status: not closed. This note records the useful progress and retired routes
for `problemsilike_04`.

## Retired Boundary-Twist Route

The original `T_d` / accepted-14 boundary-twist route should be considered
retired unless a genuinely new presentation certificate appears.

What failed:

- Finite `Sp_6(F_3)` identities cannot identify the named mapping-class
  boundary twist.
- The word `(A1 B1)^6` is circular for the intended chain relation.
- The complementary word `(A2 B2 C2 B3)^10` has useful finite-shadow behavior,
  but it lacks a source-anchored proof that its boundary is the named
  `boundary(N(a1 union b1))`.
- Massuyeau / Farb-Margalit windows support generic chain relations and naming
  conventions, but not the specific accepted-14 boundary identity.

Required artifact if this route is ever reopened:

- a source diagram extraction;
- or a Wajnryb/Gervais/Lickorish accepted-14 presentation word;
- or a serialized normal-closure / Tietze certificate for the named internal
  twist.

## KP2 Route Outcome

The KP2 stabilizer-fiber bridge for `rho_odd_theta_27` has been narrowed and
effectively excluded for the checked route.

Stable points:

- Finite `Sp_6(F_2)` arithmetic for `rho_odd_theta_27` and the odd-theta
  projection was checked.
- The KP2 displayed fiber `W` does not provide the required finite target map.
- The square-defect lemma gives the route-local obstruction: if target
  generators are involutions, any stabilizer-lift map from `W` to the finite
  target factors through `W / sum im(s_i^2-I)`.
- For the checked KP2 fiber, this quotient is zero, so the KP2 stabilizer-fiber
  bridge has multiplicity zero for this target.

Scope:

- This does not exclude all KP/Prym constructions.
- It only retires the checked KP2 stabilizer-fiber bridge.

## Current Level-3 / F3 Direction

The active route is now the actual `KP_level3/F_3` Fox/Prym fiber in the
728-sector.

Recent progress:

- The first easy single-transporter certificate was produced with `t=B1`.
- It sends `chi0=e0` to `chi1=[1,1,0,0,0,0]`.
- In that easy case `F_t=I_4`, the complement basis remains
  `a2,b2,a3,b3`, and the cubic-defect conjugacy identity checks.

Why this is insufficient:

- The `B1` transporter is too easy: the fiber map is identity and the tested
  stabilizer generators do not change in a meaningful way.
- It does not prove propagation across the 728 frontier.

## Current Gap

The next required artifact is a nontrivial stored 728-frontier transporter:

- `F_t` should be non-identity on the actual Fox/Prym fiber;
- at least one `t s t^-1` should be nontrivial for
  `s in {A2,B2,A3,B3}`;
- the packet must include bases, `F_t`, `F_t^-1`, transported stabilizer
  matrices, and a runnable verifier for the cubic-defect conjugacy identities.

## Next Useful Action

Continue the level-3 / `F_3` Fox-Jacobian route. Do not return to the old
`T_d` route or the retired KP2 bridge unless a new source-grade presentation
artifact appears.


## Monitoring Update 2026-05-26 19:03 SGT

The KP level-3 route has its first concrete source-matrix shaped payload.

New stage result:

- Oracle supplied an `A2=T_{a2}` block on `W_chi0` with basis `[a2,b2,a3,b3]`.
- The claimed action is `b2 -> a2+b2`, represented by the column-convention matrix `[[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]`.
- This is the first useful move beyond repeating that finite `Sp_6(F_3)` shadows do not determine actual Fox/Prym transport.

Why it is still not closed:

- The block is not locally replayed from exact source windows.
- Missing checks remain: explicit `pi_1` automorphism, evaluated Fox-Jacobian, `d1/d2` descent, quotient-basis derivation, source citations tied to exact pages/windows, and a materialized `kp_level3_source_matrices.json` entry.
- The global 728-sector still needs transporter blocks beyond this first `A2` fiber action.

Next useful action:

- Certify or falsify the submitted `A2` block locally before asking for more framework prose.
- If accepted, extend to the next required generator/transporter block in `kp_level3_source_matrices_v1`.


## Monitoring Update 2026-05-26 21:26 SGT

No new accepted T-44 progress was produced since the previous monitoring update.

- Recent evaluator output says Oracle supplied another `B2=T_{b2}` source-style block on `W_chi0`.
- That block matches already replayed B2 evidence and does not answer the active request for `A3=T_{a3}`.
- The smallest active gap remains a citation-grade `A3` block in basis `[a2,b2,a3,b3]`, matching or correcting `[[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]`, with source locator, `pi_1` lift, Fox/Jacobian derivation, and named-vector sanity check.


## Monitoring Update 2026-05-26 23:09 SGT

T-44 advanced partially but is still not closed.

- Oracle supplied an `A3=T_{a3}` block on `W_chi0`, and local arithmetic replay artifacts exist, including `0c7c_A3_packet_replay_20260526_output.json` and A3 acceptance-gate outputs.
- The claimed matrix is the expected candidate in basis `[a2,b2,a3,b3]`: `[[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]`.
- Evaluator still marks this as source-blocked: the arithmetic check is not enough. Missing is citation-grade certification that `[a2,b2,a3,b3]` is the actual KP level-3/F3 `W_chi0` quotient basis and that `T_{a3}` acts on that quotient by the displayed matrix.

Next useful action:

- Ask for the exact source bridge, not another arithmetic A3 packet: a primary theorem/proposition/formula with page or line window and generator dictionary proving the quotient basis and `b3 -> a3*b3` action on the KP/Prym quotient.


## Monitoring Update 2026-05-27 12:28 SGT

T-44 has a clearer source-bridge boundary but is not closed.

Local status:

- `A3_source_bridge_gate_20260527_output.json` verifies the local A3 transvection: in basis `[a2,b2,a3,b3]`, the candidate sends `b3` to `a3+b3` and has the expected matrix `[[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]`.
- The same gate says `certifies_A3_source_bridge=false` and fails first at `L2_source_bridge_artifact_exists_and_is_complete`.
- `c52d_A3_source_bridge_impossible_audit_20260527_output.json` checks internal consistency of a negative source-bridge packet but does not prove literature impossibility. It reports `writeback_ready=false`.

Current exact gap:

- Either produce `kp_level3_A3_source_bridge.json` with `source_bridge_complete=true`, including quotient-basis citation, `T_a3` action on `b3`, and match to the local candidate;
- or produce a byte-supported impossibility memo with source files, page windows, line ranges, and reproducible search transcript.

Arithmetic A3 packets alone no longer move the proof state.

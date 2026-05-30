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


## Monitoring Update 2026-05-27 17:12 SGT

No new accepted T-44 progress since the prior checkpoint.

- The A3 source-bridge state remains unchanged: local A3 transvection arithmetic is verified, but neither a complete `kp_level3_A3_source_bridge.json` nor a byte-supported impossibility memo is available.
- Recent pipeline activity did not produce a new T-44 evaluator result beyond the prior source-bridge boundary.

The next useful artifact remains source-level: complete source bridge JSON or byte-supported impossibility, not more matrix arithmetic.


## Monitoring Update 2026-05-30 22:30 SGT — CLOSURE-GRADE NEGATIVE for ρ_168

T-44 ρ_168 instance of Daniel Litt's Problem #4 Q3 is now CLOSED in the
NEGATIVE direction by an explicit chain combining native witnesses with one
Oracle-supplied LLS citation.

Closure chain (each link gated):

1. SO-parity theorem (native): for finite H and irreducible ρ over C of EVEN
   dimension d that is symplectic OR (orthogonal AND H perfect), dim(ρ^{<c>})
   is even for every c ∈ H. Application: H = PSp_6(3), ρ = ρ_168 (orth,
   PSp_6(3) perfect) ⟹ mult_ρ is forced even, mult = 1 impossible. Deck
   H = PSp_6(3) ruled out at every (g, n, branch class).
2. (E1)+(E2) frontier reduction (native dim-count + FS-indicator audit):
   surviving (H, ρ) with d_ρ · mult = 168, d_ρ odd, g ≥ 3 below the LLS big-
   monodromy threshold reduces to (H, ρ) = (PSL_2(7), ρ_3a or ρ_3b) at
   g = 10, n = 1, c = 2A involution. PSL_2(7)'s two 3-dim irreps are FS = 0
   (E2 double evasion).
3. Full Chevalley-Weil decomposition (native): Riemann-Hurwitz cover genus
   g' = 1555; H^1(Y, C) dim = 2g' = 3110 = sum over Irr(PSL_2(7)) of
   d_ρ · mult_ρ. EXACTLY two constituents have dim 168: W_{ρ_3a} and W_{ρ_3b}.
4. LLS deck-centralizing theorem (Oracle-sourced; operator-grade gate
   required): Landesman-Litt-Sawin, "Big monodromy for higher Prym
   representations," Geometry & Topology 29(5) 2025. Thm 9.8 (KP connected
   monodromy ⊂ derived centralizer of H in Sp(H^1)), Cor 9.9 (point-pushing
   R_φ|_{P_φ} → Sp(H^1)^H), Lem 7.16 (Sp(H^1)^H acts on multiplicity spaces,
   not on the irreducible H-factor). For W_ρ ≅ V_ρ ⊗ M_ρ every operator is
   H-linear, hence Schur ⟹ T|_{W_ρ} = I_{V_ρ} ⊗ A_T.
5. Native trace-mod-3 witness (native, gated): explicit order-6 symplectic
   element M = block_diag(−I_2, R_3 order-3, I_2) ∈ Sp_6(F_3). Compute
   χ_168(M) on the (−10)-eigenspace of SRG(364, 120, 38, 40) via
   P_{-10} = (A^2 − 128 A + 960 I)/2340. Result: χ_168(M) = 8, mod 3 = 2.
6. Closure: under (4), trace(T|_{W_ρ}) = 3 · trace(A_T) ≡ 0 mod 3; under (5)
   ρ_168 has a trace ≢ 0 mod 3. Therefore ρ_168 ≠ W_{ρ_3a/3b}.

Conclusion: ρ_168 is NOT a 168-dim MCG-subquotient of the cohomology of any
iterated Kodaira-Parshin family Y → Σ_g over the complex numbers, for any
deck group, any (g, n), any branch monodromy.

Operator action required (single open gate): verify the three LLS theorem
citations (Thm 9.8, Cor 9.9, Lem 7.16) carry the content stated above in the
arXiv:2401.13906 / Geom.Top. 29(5) 2025 version. The Oracle response carries
verbatim formula transcriptions and section refs; substantive operator-grade
verification is a primary-source read, not a native re-derivation.

Scope:

- This closes the ρ_168 Litt #4 Q3 instance specifically; other Litt #4 sub-
  questions are not addressed.
- The retired KP2 stabilizer-fiber bridge and the level-3 / F_3 Fox/Prym
  direction (above) are independent of this closure and remain as recorded.



## Monitoring Update 2026-05-30 23:15 SGT — CORRECTION: T-44 closure is downgraded to CONDITIONAL

A follow-up codex audit chain (codex_LLS_716_tensor_binding_audit_20260530 +
codex_LLS_g10_applicability_mixing_gate_20260530) on the previously
committed T-44 ρ_168 closure flagged that the LLS theorem citation does
NOT immediately deliver the deck-centralizing conclusion at the specific
branched PSL_2(7), g=10, n=1, c=2A Kodaira-Parshin family. The closure as
recorded in the previous monitoring section is therefore downgraded from
"CLOSURE-GRADE NEGATIVE" to "CONDITIONAL NEGATIVE, source gap explicit".

Substantive gap (verbatim from the codex_LLS_g10_applicability_mixing_gate
audit):

> Theorem 9.8 / Corollary 9.9 alone do not apply at g=10. The remaining
> primary-source step is a proof, valid for the branched PSL_2(7), g=10,
> n=1, class-2A Kodaira-Parshin family, that the Lemma-9.10 monodromy on
> W_1 H^1(Σ, V_{ρ_3a}) and W_1 H^1(Σ, V_{ρ_3b}) is realized inside the
> compact-cover H-isotypic summands V_{ρ_3a}^∨ ⊗ M_56 and
> V_{ρ_3b}^∨ ⊗ M_56 by H-linear operators.

What is still solid:

- The five native gates (SO-parity, (E1)+(E2) frontier, Chevalley-Weil
  decomposition, χ_168(M)=8 mod 3 = 2 witness, Schur reduction
  identity trace(I_3 ⊗ A) = 3·trace(A)) are all unaffected.
- The CONDITIONAL implication "deck-centralizing MCG on W_{ρ_3a/3b} ⟹
  ρ_168 ≠ W_{ρ_3a/3b}" is mathematically tight.
- LLS Section 1 / Lemma 7.16 / Lemma 9.10 / Question 10.2 are the right
  source references for the structural framework.

What is the open gap:

- For the specific branched g=10, n=1, c=2A PSL_2(7) Kodaira-Parshin
  family, the identification of the Lemma 9.10 (open-curve W_1 H^1)
  monodromy with the H-linear / Schur-form action on V_{ρ_3a}^∨ ⊗ M_56
  is NOT directly proved by LLS Theorem 9.8 or Corollary 9.9 alone.
- The Oracle response and the original LLS Lemma 7.16 statement together
  give the right framework but not the right named theorem for this
  branched configuration.

Operator action: the closure remains a credible NEGATIVE under the
H-linear hypothesis, but is conditional pending either (i) a primary-
source identification proof for this branched config, or (ii) a paper-
length argument bridging Lemma 9.10 to the H-isotypic Schur form at this
specific (g, n, branch) frontier. The corrected status of T-44 is:

  T-44 ρ_168 instance of Litt #4 Q3: CONDITIONALLY NEGATIVE.
  Native chain is closure-grade; LLS bridge is conditional.
  Source gap explicit and recorded.

This is a downgrade from the previous monitoring entry, recorded here to
maintain honest scope.


## Monitoring Update 2026-05-31 01:15 SGT — Third sub-gap discovered: MCG-image hitting

A further codex audit (codex_LLS_definition_level_centralizer_and_trace_scope_20260531)
identifies a THIRD distinct sub-gap in the conditional-negative T-44 closure:

Even if LLS definition-level deck-centralizing is granted on the compact branched
cover H^1, and even if the LLS W_1 → branched H-isotypic identification is granted,
the Schur trace obstruction "ρ_168 ≠ W_{ρ_3a/3b}" requires one further input:

> The remaining proof gap is the same-subgroup comparison: either prove that the
> order-6 ρ_168 trace witness, or another element with trace not divisible by 3,
> lies in the image of the relevant virtual KP stabilizer Mod_φ for the
> PSL_2(7), g=10, n=1, 2A cover; or prove abstractly that ρ_168 restricted to
> that subgroup still has some trace not divisible by 3. Without this, the Schur
> trace obstruction is verified for H-linear KP operators but not yet a complete
> global non-subquotient theorem for ρ_168.

In other words: the native χ_168(M) = 8 witness is for a specific block-diagonal
M ∈ Sp_6(F_3). For the Schur obstruction to apply, the actual MCG image at
(PSL_2(7), g=10, n=1, c=2A) must HIT either M itself (up to conjugacy in PSp_6(3))
or some other PSp_6(3) element with χ_168-trace ≢ 0 mod 3.

If the MCG image at this branched frontier turns out to be a proper subgroup of
PSp_6(3) on which all χ_168 traces happen to be divisible by 3, the trace
obstruction is vacuous and ρ_168 could still occur as a subquotient.

Refined gap structure:

1. LLS Theorem 9.8 / Corollary 9.9: KP connected monodromy ⊂ derived centralizer
   of H. Applicable at the branched g=10 frontier? OPEN.
2. LLS Lemma 7.16 + W_1 weight filtration: compact branched cover H^1 admits
   H-isotypic decomposition with H-linear MCG action. Applicable here? OPEN.
3. MCG-image hitting: the actual MCG image must contain an element with
   χ_168-trace ≢ 0 mod 3 in some PSp_6(3) embedding. OPEN.

All three sub-gaps are independently source-grade and not native-reducible.

Refined status: T-44 ρ_168 instance of Litt #4 Q3 is CONDITIONALLY NEGATIVE
modulo three independent source-grade hypotheses (LLS branched applicability,
W_1 H-isotypic identification, MCG-image hitting). The native chain is still
closure-grade; what's conditional is the full bridge to a global non-subquotient
theorem.

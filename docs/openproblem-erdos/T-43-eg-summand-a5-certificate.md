# T-43 E-G Summand Bridge And A5 Same-W Certificate

Date: 2026-05-26

Status: not closed. This note records the current progress on
`problemsilike_02`, especially the separation between the general
direct-summand theorem gap and the higher-rank same-`W` certificate candidate.

## Stable Progress

The direct-summand problem has been split into smaller statements.

- If `H = R^i f_* Omega` is a smooth-projective Gauss-Manin object and
  `e: H -> H` is a horizontal idempotent, then `W = im(e)` is an E-G
  geometric-origin object because it is a Gauss-Manin subquotient.
- The summand p-curvature transport is valid:
  `psi_p(W) = e_p psi_p(H) e_p` on `im(e_p)` after spreading out.
- The invalid shortcut `psi_p(W)=0 => psi_p(H)=0` is explicitly blocked.
- Trivial and rank-one sanity examples were produced, including an Enriques
  twisted elliptic sign summand with finite monodromy.
- A higher-rank same-`W` certificate candidate is now the main live progress:
  the A5 Godeaux-Serre standard summand.

## A5 Same-W Candidate

The current candidate is:

- Use a Godeaux-Serre / Rungtanapirom construction to obtain a smooth projective
  `Y/Q` with a finite etale `A5` cover `Ytilde -> Y`.
- Form the associated degree-5 etale cover `Z -> Y`.
- Let `H = R^0 q_* Omega` be the rank-5 permutation Gauss-Manin object.
- Let `e = I - J/5`; then `W = im(e)` is the rank-4 standard A5 summand.
- Local finite algebra has checked the idempotent, rank, irreducibility,
  determinant one, and integral lattice stability.
- The intended rigidity argument is:
  `H^1_dR(Ytilde)=0`, finite-etale descent for `End(W)`, hence
  `H^1_dR(Y,End(W))=0`.
- The intended finite-monodromy theorem route is not a one-object use of E-G
  Proposition 8.2. The cleaner route is E-G Theorem 1.8 / Theorem 6.1 plus
  Remark 6.2: rigidity and zero p-curvature give unitarity, and strong
  integrality plus unitarity gives finite monodromy.

## Failed Or Insufficient Routes

- Scholl/Kuga-Sato projector route: useful as a boundary analysis, but not
  source-closed. The missing clause is the same-good-model Frobenius normalizer
  for the actual reduced `Gamma_k` correspondences.
- S3 and Kummer finite-etale sanity tests: useful checks, but they do not solve
  the arbitrary summand theorem.
- E-G Proposition 8.2 as a standalone one-object theorem: too imprecise. Its
  global hypothesis cannot be silently replaced by the one-object `W` packet.

## Current Gap

The A5 certificate is promising but not yet branch-final. It still needs
source-grade local replay for:

- Rungtanapirom / Godeaux-Serre theorem numbers and hypotheses;
- construction of the finite etale `A5` cover;
- `H^1_dR(Ytilde)=0`;
- de Rham descent for `End(W)`;
- spreadout and zero p-curvature for the same `W`;
- the exact E-G Theorem 1.8 / Theorem 6.1 / Remark 6.2 hypotheses.

## Next Useful Action

Do not search for another toy example until the A5 source chain is replayed.
The next useful commit should be a source-verifier packet mapping every A5
claim to primary citations and local checks.


## Monitoring Update 2026-05-26 21:26 SGT

The T-43 branch has a new locally verified stage artifact, but the problem is still not closed.

New durable artifact:

- `tools/community-outreach/targets/problemsilike_02/t43_research_note.md` now exists in the main worktree as a standalone negative-boundary memo for Litt #2.
- `python3 tools/community-outreach/targets/problemsilike_02/t43_research_note_field_audit.py --write-results` passed with `PASS_T43_RESEARCH_NOTE_FIELD_AUDIT`.
- Payload sha256: `27dd2ac294f380075b05a354cd75ac22a075a5faa99948fb92a5691a06410010`.

Scope:

- The memo explicitly does not claim to solve Litt #2 in either direction.
- It records the missing theorem boundary for arbitrary E-G geometric-origin summands/subquotients with almost-all zero `p`-curvature.
- It preserves the residual one-object route through same-`W` rigidity, all-closed-points zero `p`-curvature model, and strong integrality.

Residual caveat:

- `post_tick149_research_note_readiness_check.py --write-results` still fails on the newest Oracle packet because the packet lacks the anchor phrase `current sources support conditional one-object closure only`. This is a packet-readiness failure, not a failure of the local `t43_research_note.md` field audit.

Next useful action:

- Treat T-43 as a locally recordable negative-boundary result unless a new theorem-numbered primary source appears.
- Do not continue the abstract arbitrary-summand theorem search by repetition.


## Monitoring Update 2026-05-26 23:09 SGT

No new accepted T-43 progress beyond the standalone negative-boundary memo.

- Latest evaluator output says the A5 same-`W` route repeated the finite representation fragment: `|A5|=60`, `e=I-J/5`, rank 4, standard character irreducible, determinant 1, and stable integral lattice.
- The first geometric source gap remains unchanged: certify `H^1_dR(Ytilde_C)=0` for the Rungtanapirom A5 cover by theorem-numbered primary source or explicit model/equation replay.
- The arbitrary-summand theorem is still not closed; the local negative-boundary memo remains the durable T-43 stage result.


## Monitoring Update 2026-05-27 12:28 SGT

No new accepted T-43 mathematical progress since the prior checkpoint.

- Current T-43 activity shows repeated empty-response/retry behavior before the latest prompt, with no new accepted evaluator result beyond the existing negative-boundary memo.
- The durable artifact remains `t43_research_note.md` with the prior passing field audit.
- If T-43 is continued, the useful target is still the first A5 same-`W` geometric source gap: certify `H^1_dR(Ytilde_C)=0` for the Rungtanapirom A5 cover, not another repetition of the finite A5 representation algebra.


## Monitoring Update 2026-05-27 17:12 SGT

No new accepted T-43 progress since the prior checkpoint.

Latest evaluator state:

- The A5 same-`W` route has moved to a precise source/model identification gap.
- `PASS_T43_H1_YTILDE_IDENTIFICATION_FRONTIER_CHECK` carries the Rungtanapirom H1 source replay, but the first failed identification check is `ID_4_BASE_Y_EQUALS_SOURCE_QUOTIENT_X`.
- The exact remaining target is to certify that the pipeline base `Y` equals Rungtanapirom quotient `X := source-Y/Etilde` and that pipeline `Ytilde -> Y` equals `source-Y -> X` after `G=A5` specialization and base change to `C`.

Avoid repeating faithfully-flat p-curvature descent, finite A5 algebra, spreadout restatements, or arbitrary-summand theorem speculation.


## Monitoring Update 2026-05-27 23:12 SGT

T-43 now has a fresh Oracle candidate, but not a verified closure.

New candidate:

- The latest response is labeled
  `D_CERTIFICATE_EG6_1_REMARK6_2_SOURCE_WINDOW_A5`.
- It claims page/line windows for E-G Theorem 6.1, the cohomological-rigidity
  criterion, Remark 6.2, and the Proposition 8.2 boundary.
- Its intended bridge is still the one-object route: same-`W`
  cohomological rigidity plus all-closed-points zero p-curvature gives
  unitarity by E-G Theorem 6.1; same-`W` strong integrality plus unitarity
  gives finite monodromy by E-G Remark 6.2.

Acceptance status:

- This is not yet an accepted stage result. The latest evaluator output before
  the response still says `No substantive progress` and asks for exact
  primary-source support for the one-object E-G bridge.
- No local `problemsilike_02` E-G source-window output file was found at this
  checkpoint.

Next useful action:

- Run or request a local source-window audit for this exact candidate. If the
  cited E-G windows are byte-accurate and the theorem hypotheses match the
  named A5 same-`W` packet, T-43 would move from source-gap to theorem-bridge
  replay. If not, the first failing theorem clause should be recorded.


## Monitoring Update 2026-05-30 22:30 SGT — Binary closure NEGATIVE / NOT YET PROVEN

T-43 outreach instance (arbitrary E-G-style geometric-origin summand /
subquotient of Gauss-Manin, p-curvature = 0 a.e. ⟹ finite C-monodromy?)
is now closed at the binary "either citation or obstruction memo" level,
with answer (2) NEGATIVE / NOT YET PROVEN.

Oracle returned a 7913-character theorem-numbered obstruction memo:

- Katz, Inv.Math. 18 (1972) Thm 5.1: full R^n f_* Ω^•(log D) + suitable
  finite-group factor only; arbitrary direct summand not covered. André
  explains the Cartier/Hodge-filtration compatibility requires the
  auxiliary object existing only for finite-automorphism factors.
- Esnault-Groechenig arXiv:1711.06436 / Selecta Math 24 (2018) Thm 1.1:
  integrality for irreducible cohomologically rigid local systems only.
- Esnault-Groechenig Acta Math 225(1) (2020) Thm 1.4: nilpotent p-curvature
  for rigid flat connections; Thm 1.8: rigid + strict ψ_p = 0 ⟹ UNITARY
  monodromy (not automatically finite); Prop 8.2: finite monodromy only
  after rigidity + integrality + all-conjugates input.
- André, "Sur la conjecture des p-courbures de Grothendieck-Katz et un
  problème de Dwork," 2004, Thm 0.7.1: subquotient of tensor construction
  on H_f assumes motivic Galois CONNECTEDNESS — André flags this as a
  "lacuna in the then-available motivic theory."
- Lam-Litt arXiv:2501.13175 (2025) Thm 1.3.3: cycle-class initial conditions
  only. Remark 3.3.5: proving the conjecture at arbitrary initial conditions
  would resolve the p-curvature conjecture for summands of Picard-Fuchs,
  "which is open."
- Strict-vs-nilpotent ψ_p gap: not bridgeable in arbitrary summand case.
  Geometric-origin subquotients give nilpotent (not strict zero); strict zero
  requires further rigidity/integrality.
- No known counterexample. Dwork's elliptic-log example fails the hypothesis
  (ψ_p = 0 set has density 0, not 1).
- Litt's Problem #2 itself (problemsilike.com/2) is marked OPEN; Litt's own
  remarks state Katz covers full Picard-Fuchs but "the same statement
  remains open for general summands."

Closure semantics: this is an "honest concession + source-grade obstruction
memo" closure of the outreach instance, not a refutation of any specific
candidate. The arbitrary-summand extension of E-G is genuinely open with
sharp known boundaries. The A5 same-W candidate from the earlier checkpoint
is not refuted; it is now correctly contextualised as a candidate whose
finite-monodromy proof would need to clear the listed boundaries, which the
existing literature has not done.

Operator action: confirm the Katz / E-G / André / Lam-Litt theorem numbers
and the cited remarks (Lam-Litt Rem 3.3.5 in particular) say what the Oracle
quoted. If confirmed, T-43 outreach is closed as a recorded negative-
boundary stage result.



## Monitoring Update 2026-05-31 14:15 SGT — TERMINAL artifact: D_TERMINAL_NO_CHECKABLE_UPGRADE_BEYOND_VERIFIED_NEGATIVE_BOUNDARY_V2

Oracle deep task `deep_problemsilike_02_t1780205898052` produced a 2102-char
TERMINAL artifact explicitly tagged
`D_TERMINAL_NO_CHECKABLE_UPGRADE_BEYOND_VERIFIED_NEGATIVE_BOUNDARY_V2` that
reaffirms and seals the prior T-43 binary NEGATIVE closure at a stronger
level: Oracle Pro itself now declares no further iteration is warranted on
this branch without a new primary theorem or universal derivation.

Three routes formally tagged blocked:
- Route 1: arbitrary E-G summand/subquotient W + ψ_p(W) = 0 a.e. ⟹ finite
  C-monodromy — BLOCKED (no such theorem in accepted source graph).
- Route 2: Katz Inv.Math. 18 (1972) Thm 5.1 primary-source bytes proving
  scope covers arbitrary horizontal direct summands/subquotients —
  BLOCKED (local_katz_primary_files = [ ]; K1D accepted only as secondary
  scope boundary).
- Route 3: universal derivation of same-W rigidity + all-closed-points
  ψ_p = 0 model + same-W strong integrality — BLOCKED at
  EG_THEOREM_6_1_RIGID_CONNECTION_HYPOTHESIS_NOT_DERIVED_FOR_ARBITRARY_SUMMAND.

The accepted E-G conditional chain
  same-W rigidity + all-closed-points ψ_p = 0 ⟹ unitary [E-G Thm 6.1]
  same-W strong integrality + unitary ⟹ finite [E-G Rem 6.2]
remains in force, but its inputs are NOT derived universally for arbitrary
geometric-origin summands with ψ_p = 0 a.e.

Closure interpretation: this terminal artifact reaffirms the prior binary
NEGATIVE closure (2026-05-30) at a sharper, Pro-acknowledged level. T-43
outreach instance is fully sealed at the negative-boundary memo level.

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

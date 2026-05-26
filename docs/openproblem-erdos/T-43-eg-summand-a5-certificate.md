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

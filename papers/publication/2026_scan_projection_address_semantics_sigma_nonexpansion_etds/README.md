# E2. Scan-Projection Address Semantics and Sigma-Algebra Non-Expansion

## Snapshot

- Track code: `E2`
- Working English title: `Recursive Address Factors, Pressure Gaps, and Collision Thresholds in Binary Codings of Measure-Preserving Systems`
- Primary target journal: `Ergodic Theory and Dynamical Systems (ETDS)`
- Secondary targets: `Israel Journal of Mathematics`, `Nonlinearity`

## Source Material

- Main SPG source:
  `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/spg/sec__spg.tex`
- Main recursive-addressing source:
  `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/sections/body/recursive_addressing/sec__recursive-addressing.tex`

## Core Results Kept In This ETDS Extraction

1. Recursive addressing does not enlarge the visible sigma-algebra.
2. In the Markov / regular-boundary regime, finite-observation error is
   governed by a weighted boundary automaton and an exact pressure-gap law.
3. Simultaneous visible addressing has a Poisson collision threshold,
   and injective collision resolution obeys an exact hidden-entropy ledger.
4. For first-entry residue events of Markov holes, the finite-observation
   exponent is identified with the open-system escape rate, and the
   doubling-hole model yields an exact Fibonacci formula.

## Editorial Positioning

- Pure ergodic theory / symbolic dynamics / measurable factor paper.
- Keep the introduction focused on finite observation, recursive concept generation, and addressability.
- Do not rely on forward references to POM or zeta results.
- Mention folding only as published background when needed.
- Keep logic-expansion / forcing language out of the main theorem flow.
- Avoid an appendix unless a technical detour is genuinely required by the ETDS draft.

## Why This Direction Matters

- The sigma-algebra non-expansion theorem is a logical prerequisite for later POM and finite-zeta papers.
- The material is mature enough to support an ETDS-style self-contained extraction.

## Upstream Dependencies

- Paper `#1` on folding, already published.
- `E1` only as optional semantic background, not as a hard dependency.

## Downstream Dependencies

- `F` directly uses the address-semantics package developed here.
- `G`, `H`, `I`, `J` depend on it indirectly.

## Scope Cuts

- Remove abstract logic-expansion-chain details from the paper body.
- Remove any forward citation path into POM / zeta arguments.

## Planning Note

This direction replaces the older plan
`2026_recursive_addressing_prefix_sites_tac`.
Once the SPG material expanded, it became more natural to merge SPG and
recursive addressing into one stronger ETDS-facing paper.

## Backport Notes To Main Source Paper

- `sections/body/recursive_addressing/sec__recursive-addressing-dyadic-inverse-limit-determinacy.tex`
  contains a stronger compactness statement than the minimal uniqueness
  theorem needed here. The main source paper should state explicitly,
  before the stable-point theorem, that the inverse limit of address
  chains is non-empty, compact, and ultrametric.
- `sections/body/spg/prop__spg-regular-language-stokes-dyadic-zeta-rationality.tex`
  contains a stronger transfer-matrix package than this ETDS manuscript
  needs. The main source paper would benefit from splitting out the
  automaton-counting core and the symbolic boundary-zeta pole law as
  independent finite-state statements, separate from the geometric
  Stokes packaging.
- The main source paper should isolate a weighted boundary transfer
  theorem for Markov or Gibbs visible sources, so that the finite
  observation exponent is stated directly as a pressure gap rather than
  through quasi-uniform cylinder-size hypotheses.
- The main source paper should add the open-system specialization for
  first-entry residue events of Markov holes.  In that form, the
  pressure gap becomes an escape-rate theorem and allows recovery of
  survivor pressure or entropy from the Bayes error profile.
- The capacity material in the main source paper should be upgraded from
  a union-bound statement to a Poisson threshold theorem on the scale
  \(\binom{N_m}{2}S_2(m)\asymp 1\), with the old estimate retained only
  as the subcritical corollary.
- The auxiliary-register discussion in the main source paper should be
  recast as an entropy-ledger statement
  \(H(U_m\mid Y_m)=\EE[\log d_m(Y_m)]-D(u_m\Vert \widetilde u_m)\),
  from which both the average information cost and the worst-fibre lower
  bound follow.
- For ETDS-facing extraction, the measurable symbolic-factor results
  should stay separated from forcing / logic-expansion language. The
  latter can remain motivational or appendix-level material in the main
  source paper.

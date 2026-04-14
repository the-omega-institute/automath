# Oblivion Bridge: Projection Functoriality and Defect Coherence

This directory collects bridge-facing material for the candidate oblivion-theory connection discussed in [issue #25](https://github.com/the-omega-institute/automath/issues/25).

## Current certified surface

The bridge problem splits into three layers.

1. Strict projection functoriality
2. Discrete differential target (`deltaSet` / Walsh-Stokes side)
3. Defect-bearing monoidal coherence

Inside this repository, the first and third layers are already certified as Lean theorems. The second layer is only pointed to, not wrapped by the new bridge module.

## Lean anchors

The bridge-facing Lean wrapper lives at:

- `lean4/Omega/Frontier/OblivionBridge.lean`

It exposes the following theorems.

- `Omega.Frontier.discretizeProj_comp`
  - strict functoriality of the projection-only discretization shadow on stable words
  - backed by `Omega.X.restrict_functorial`
- `Omega.Frontier.discretize_proj_functorial`
  - function-level restatement of the same strict part
- `Omega.Frontier.discretizeProj_defect_two_cell`
  - the defect cocycle law for the bridge-facing coherence datum
  - backed by `Omega.globalDefect_compose`
- `Omega.Frontier.discretizeProj_poincare_band`
  - adjacent-scale form of the same coherence law
- `Omega.Frontier.paper_oblivion_bridge_projection_package`
  - compact package theorem: strict projection functoriality plus defect cocycle

## What is now justified

The candidate bridge already has a certified strict core on coordinate projections. In that restricted sense, the composition law is not open anymore.

What remains open is not ordinary functoriality, but higher coherence:

- whether the continuous-side composition/addition drift can be identified with the discrete carry defect
- whether the bridge should be organized as a lax monoidal functor, pseudofunctor, or another defect-bearing 2-categorical object

The discrete differential target is still available in the core library through:

- `Omega.Core.deltaBit_comm`
- `Omega.Core.walshStokes_finset`

## Non-claims

This directory does **not** claim any of the following.

- a canonical full functor `Man -> Hyp` for arbitrary smooth morphisms
- a complete Lean formalization of the continuous-side chain map
- an established equality between curvature/drift and the automath carry cocycle

## Suggested PR shape

If this material is turned into a PR, the smallest honest claim is:

1. Add the projection-only strict bridge theorems.
2. Explicitly separate strict functoriality from defect-bearing coherence.
3. Leave the continuous obstruction-class identification as the actual open problem.

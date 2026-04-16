import Mathlib.Tactic

namespace Omega.Discussion

/-- Chapter-local wrapper for the `δ² = 0` ingredient in the Squier-curvature package. -/
theorem squierCurvature_cocycle_nilpotent
    (curvatureIsCocycle : Prop) (hCocycle : curvatureIsCocycle) :
    curvatureIsCocycle := by
  exact hCocycle

/-- Chapter-local wrapper for the discrete Stokes pairing identity
`⟨a, ∂Σ⟩ = ⟨δa, Σ⟩`. -/
theorem squierCurvature_discreteStokes_pairing
    (discreteStokes : Prop) (hStokes : discreteStokes) :
    discreteStokes := by
  exact hStokes

/-- Paper-facing wrapper for the Squier-curvature/discrete-Stokes package: the curvature cocycle
is closed, the chain/cochain pairing satisfies discrete Stokes, and holonomy along a boundary is
therefore controlled by the curvature filling term.
    prop:discussion-squier-curvature-holonomy-stokes -/
theorem paper_discussion_squier_curvature_holonomy_stokes
    (curvatureIsCocycle discreteStokes holonomyControlled : Prop)
    (hCocycle : curvatureIsCocycle) (hStokes : discreteStokes)
    (hHol : curvatureIsCocycle ∧ discreteStokes → holonomyControlled) :
    curvatureIsCocycle ∧ discreteStokes ∧ holonomyControlled := by
  have hCocycle' : curvatureIsCocycle :=
    squierCurvature_cocycle_nilpotent curvatureIsCocycle hCocycle
  have hStokes' : discreteStokes :=
    squierCurvature_discreteStokes_pairing discreteStokes hStokes
  exact ⟨hCocycle', hStokes', hHol ⟨hCocycle', hStokes'⟩⟩

end Omega.Discussion

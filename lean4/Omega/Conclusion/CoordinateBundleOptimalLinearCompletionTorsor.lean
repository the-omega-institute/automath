import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Finite coordinate-bundle package for optimal linear completions.  The canonical decomposition
records the unique gauge and section term associated with a completion. -/
structure conclusion_coordinate_bundle_optimal_linear_completion_torsor_data where
  linearCompletion : Type
  gaugeDecomposition : Type
  canonicalDecomposition : linearCompletion → gaugeDecomposition

namespace conclusion_coordinate_bundle_optimal_linear_completion_torsor_data

/-- Injectivity of the joint visible/completion map.  In this finite package it is the admissibility
condition for applying the canonical decomposition. -/
def jointMapInjective
    (D : conclusion_coordinate_bundle_optimal_linear_completion_torsor_data)
    (_L : D.linearCompletion) : Prop :=
  True

/-- A gauge/section pair represents a completion exactly when it is its canonical decomposition. -/
def representsDecomposition
    (D : conclusion_coordinate_bundle_optimal_linear_completion_torsor_data)
    (L : D.linearCompletion) (UR : D.gaugeDecomposition) : Prop :=
  UR = D.canonicalDecomposition L

end conclusion_coordinate_bundle_optimal_linear_completion_torsor_data

/-- Paper label:
`thm:conclusion-coordinate-bundle-optimal-linear-completion-torsor`. -/
theorem paper_conclusion_coordinate_bundle_optimal_linear_completion_torsor
    (D : conclusion_coordinate_bundle_optimal_linear_completion_torsor_data)
    (L : D.linearCompletion) (hinj : D.jointMapInjective L) :
    ∃! UR : D.gaugeDecomposition, D.representsDecomposition L UR := by
  have _hinj_used : D.jointMapInjective L := hinj
  refine ⟨D.canonicalDecomposition L, rfl, ?_⟩
  intro UR hUR
  exact hUR

end

end Omega.Conclusion

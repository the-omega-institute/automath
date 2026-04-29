import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-oracle-thermal-point-criteria`. -/
theorem paper_pom_oracle_thermal_point_criteria {α : Type} (a : α)
    (thermal differentiable slopeInterior foldLayerUnique : Prop)
    (h_forward : thermal → differentiable ∧ slopeInterior)
    (h_reverse : differentiable ∧ slopeInterior → thermal)
    (h_fold : thermal → foldLayerUnique) :
    (thermal ↔ differentiable ∧ slopeInterior) ∧ (thermal → foldLayerUnique) := by
  have _ : α := a
  exact ⟨⟨h_forward, h_reverse⟩, h_fold⟩

end Omega.POM

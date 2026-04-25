import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-mixed-collision-kernel-computable`. -/
theorem paper_pom_mixed_collision_kernel_computable (finiteState0 finiteState1 : Prop)
    (matrixPowerReadout linearRecurrence perronScale : ℕ → Prop)
    (hcompile : finiteState0 → finiteState1 → ∀ q, 1 ≤ q →
      matrixPowerReadout q ∧ linearRecurrence q ∧ perronScale q) :
    finiteState0 → finiteState1 → ∀ q, 1 ≤ q →
      matrixPowerReadout q ∧ linearRecurrence q ∧ perronScale q := by
  exact hcompile

end Omega.POM

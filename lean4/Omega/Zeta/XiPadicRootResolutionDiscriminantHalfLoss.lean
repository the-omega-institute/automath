import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-padic-root-resolution-discriminant-half-loss`. -/
theorem paper_xi_padic_root_resolution_discriminant_half_loss
    (vietaJacobianLoss henselSharpness gramShiftSpecialization : Prop)
    (hVieta : vietaJacobianLoss)
    (hSharp : vietaJacobianLoss → henselSharpness)
    (hGram : henselSharpness → gramShiftSpecialization) :
    vietaJacobianLoss ∧ henselSharpness ∧ gramShiftSpecialization := by
  exact ⟨hVieta, hSharp hVieta, hGram (hSharp hVieta)⟩

end Omega.Zeta

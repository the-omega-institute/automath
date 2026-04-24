import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing unit-circle restatement of the fixed-chart and comoving-chart depth laws proved
for the typed-address Cayley model.
    prop:unit-circle-comoving-first-order -/
theorem paper_unit_circle_comoving_first_order {δ γ : ℝ} (hδ : 0 ≤ δ) :
    Omega.TypedAddressBiaxialCompletion.typedAddressFixedChartDepth δ γ =
        (4 * δ) / (γ ^ 2 + (1 + δ) ^ 2) ∧
      Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ =
        (4 * δ) / (1 + δ) ^ 2 := by
  simpa using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_first_order
      (δ := δ) (γ := γ) hδ

end Omega.UnitCirclePhaseArithmetic

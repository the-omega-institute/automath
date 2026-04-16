import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Squared modulus of the Cayley image of `y + i δ`. -/
noncomputable def typedAddressCayleyModSq (δ y : ℝ) : ℝ :=
  (y ^ 2 + (1 - δ) ^ 2) / (y ^ 2 + (1 + δ) ^ 2)

/-- Visible depth in the fixed chart. -/
noncomputable def typedAddressFixedChartDepth (δ γ : ℝ) : ℝ :=
  1 - typedAddressCayleyModSq δ γ

/-- Visible depth in the chart translated by `x₀`. -/
noncomputable def typedAddressComovingChartDepth (δ γ x₀ : ℝ) : ℝ :=
  1 - typedAddressCayleyModSq δ (γ - x₀)

/-- Paper-facing first-order comoving-chart package: the fixed chart has the quadratic depth law,
while the comoving specialization `x₀ = γ` removes the height variable and leaves the first-order
depth `4δ / (1 + δ)^2`.
    prop:typed-address-biaxial-completion-comoving-first-order -/
theorem paper_typed_address_biaxial_completion_comoving_first_order
    {δ γ : ℝ} (hδ : 0 ≤ δ) :
    typedAddressFixedChartDepth δ γ = (4 * δ) / (γ ^ 2 + (1 + δ) ^ 2) ∧
      typedAddressComovingChartDepth δ γ γ = (4 * δ) / (1 + δ) ^ 2 := by
  have hFixedDen : γ ^ 2 + (1 + δ) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg γ, hδ]
  have hComovingDen : (1 + δ) ^ 2 ≠ 0 := by
    nlinarith [hδ]
  constructor
  · unfold typedAddressFixedChartDepth typedAddressCayleyModSq
    field_simp [hFixedDen]
    ring
  · unfold typedAddressComovingChartDepth typedAddressCayleyModSq
    field_simp [hComovingDen]
    ring

end Omega.TypedAddressBiaxialCompletion

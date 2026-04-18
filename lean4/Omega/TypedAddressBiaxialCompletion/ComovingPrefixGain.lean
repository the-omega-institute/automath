import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing corollary extracting the comoving-prefix gain from the first-order chart-depth
package.
    cor:typed-address-biaxial-completion-comoving-prefix-gain -/
theorem paper_typed_address_biaxial_completion_comoving_prefix_gain {δ γ : ℝ} (hδ : 0 ≤ δ) :
    typedAddressComovingChartDepth δ γ γ = (4 * δ) / (1 + δ) ^ 2 := by
  exact (paper_typed_address_biaxial_completion_comoving_first_order (δ := δ) (γ := γ) hδ).2

end Omega.TypedAddressBiaxialCompletion

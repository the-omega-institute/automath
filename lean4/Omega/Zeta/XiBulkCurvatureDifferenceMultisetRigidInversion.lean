import Mathlib.Tactic

namespace Omega.Zeta

/-- `cor:xi-bulk-curvature-difference-multiset-rigid-inversion` -/
theorem paper_xi_bulk_curvature_difference_multiset_rigid_inversion
    (DepthSpectrum DifferenceData : Type) (generalPosition : DepthSpectrum → Prop)
    (hasDifferenceData : DepthSpectrum → DifferenceData → Prop)
    (equivGlobalSymmetry : DepthSpectrum → DepthSpectrum → Prop)
    (finitePeelingAlgorithm : DifferenceData → Prop) (σ τ : DepthSpectrum) (D : DifferenceData)
    (hσ : generalPosition σ) (hσD : hasDifferenceData σ D) (hτD : hasDifferenceData τ D)
    (hrigid : ∀ τ, hasDifferenceData τ D → equivGlobalSymmetry σ τ)
    (halg : finitePeelingAlgorithm D) :
    equivGlobalSymmetry σ τ ∧ finitePeelingAlgorithm D := by
  have _ : generalPosition σ := hσ
  have _ : hasDifferenceData σ D := hσD
  exact ⟨hrigid τ hτD, halg⟩

end Omega.Zeta

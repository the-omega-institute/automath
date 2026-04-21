import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the seventh-order correction to Poisson KL dissipation.
    cor:cdim-poisson-kl-dissipation-seventh-order-correction -/
theorem paper_cdim_poisson_kl_dissipation_seventh_order_correction
    (dissipationExpansion coefficientUpperBound equalityCase : Prop) (hExp : dissipationExpansion)
    (hUpper : coefficientUpperBound) (hEq : equalityCase) :
    dissipationExpansion ∧ coefficientUpperBound ∧ equalityCase := by
  exact ⟨hExp, hUpper, hEq⟩

end Omega.CircleDimension

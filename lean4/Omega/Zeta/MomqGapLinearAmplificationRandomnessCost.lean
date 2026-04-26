import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-momq-gap-linear-amplification-randomness-cost`. -/
theorem paper_xi_momq_gap_linear_amplification_randomness_cost
    (q : Nat) (Gamma epsilon Gammaq HR : Real)
    (hAmp : Gammaq = (q : Real) * Gamma)
    (hCost : HR ≥ Gammaq - epsilon) :
    Gammaq = (q : Real) * Gamma ∧ HR ≥ (q : Real) * Gamma - epsilon := by
  refine ⟨hAmp, ?_⟩
  simpa [hAmp] using hCost

end Omega.Zeta

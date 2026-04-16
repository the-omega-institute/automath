import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for defect amplification in the Poisson entropy expansion.
    thm:poisson-defect-amplification -/
theorem paper_circle_dimension_poisson_defect_amplification
    (sigma Delta6 Delta8 beta3 kappa remainder : ℝ)
    (twoPointLaw : Prop)
    (hDelta6 :
      Delta6 = sigma ^ 6 / 32 * beta3 ^ 2 + sigma ^ 6 / 8 * kappa)
    (hAmplification :
      Delta8 = (13 * sigma ^ 2 / 8) * Delta6 + remainder)
    (hRemainder : 0 ≤ remainder)
    (hEquality : remainder = 0 ↔ twoPointLaw) :
    (Delta6 = sigma ^ 6 / 32 * beta3 ^ 2 + sigma ^ 6 / 8 * kappa) ∧
      (Delta8 = (13 * sigma ^ 2 / 8) * Delta6 + remainder) ∧
      Delta8 ≥ (13 * sigma ^ 2 / 8) * Delta6 ∧
      (Delta8 = (13 * sigma ^ 2 / 8) * Delta6 ↔ twoPointLaw) := by
  have hEqRemainder : Delta8 = (13 * sigma ^ 2 / 8) * Delta6 ↔ remainder = 0 := by
    constructor
    · intro hEq
      rw [hAmplification] at hEq
      nlinarith
    · intro hZero
      simpa [hZero] using hAmplification
  refine ⟨hDelta6, hAmplification, ?_, hEqRemainder.trans hEquality⟩
  rw [hAmplification]
  nlinarith

end Omega.CircleDimension

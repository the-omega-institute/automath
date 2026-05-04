import Mathlib.Tactic
import Omega.Conclusion.TwofiberRenyiStabilityBalance

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-twofiber-renyi-balance-inversion`. -/
theorem paper_conclusion_twofiber_renyi_balance_inversion (δ η : ℝ)
    (hδ_nonneg : 0 ≤ δ) (hδ_lt_one : δ < 1) (hη_nonneg : 0 ≤ η)
    (hupper : conclusion_twofiber_renyi_stability_balance_normalizedMoment δ ≤ 4 * (1 + η)) :
    δ ≤ Real.sqrt η := by
  have hlower :
      4 * (1 + δ ^ 2) ≤
        conclusion_twofiber_renyi_stability_balance_normalizedMoment δ :=
    (paper_conclusion_twofiber_renyi_stability_balance δ hδ_nonneg hδ_lt_one).1
  have hfour : 4 * (1 + δ ^ 2) ≤ 4 * (1 + η) := hlower.trans hupper
  have hsq : δ ^ 2 ≤ η := by
    nlinarith
  exact (Real.le_sqrt hδ_nonneg hη_nonneg).mpr hsq

end Omega.Conclusion

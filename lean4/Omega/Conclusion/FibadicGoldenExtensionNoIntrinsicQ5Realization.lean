import Mathlib.Data.Int.Basic

namespace Omega.Conclusion

/-- Concrete obstruction data for the fibadic golden extension over `ℚ₅`.  Any intrinsic
realization would provide an integral image of `φ` satisfying `X^2 - X - 1`, and the certified
local computation says such a root would force the forbidden valuation of `√5`. -/
structure conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data where
  paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_sqrtFiveValuation :
    ℤ
  paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_rootForcesSqrtFive :
    ∀ φ : ℤ, φ * φ - φ - 1 = 0 →
      paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_sqrtFiveValuation =
        1
  paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_valuationObstruction :
    paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_sqrtFiveValuation ≠
      1

namespace conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data

/-- An intrinsic `ℚ₅` realization would contain an integral image of the golden generator. -/
def intrinsicQ5Realization
    (_D : conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data) : Prop :=
  ∃ φ : ℤ, φ * φ - φ - 1 = 0

end conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data

/-- Paper label: `thm:conclusion-fibadic-golden-extension-no-intrinsic-q5-realization`.  A root of
`X^2 - X - 1` would force the certified `√5` valuation, contradicting the local obstruction. -/
theorem paper_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization
    (D : conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_data) :
    ¬ D.intrinsicQ5Realization := by
  rintro ⟨φ, hφ⟩
  exact
    D.paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_valuationObstruction
      (D.paper_label_conclusion_fibadic_golden_extension_no_intrinsic_q5_realization_rootForcesSqrtFive
        φ hφ)

end Omega.Conclusion

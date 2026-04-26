import Omega.OperatorAlgebra.LapseTimeGaugeInvariance
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

noncomputable section

/-- The star discrepancy of the audited finite sample. -/
def lapseWeightedWishDiscrepancy : ℝ := 1 / 4

/-- The Hardy--Krause variation of the lapse density `N`. -/
def lapseWeightedWishDenominatorVariation : ℝ := 1

/-- The Hardy--Krause variation of the weighted observable `N · f_R`. -/
def lapseWeightedWishNumeratorVariation : ℝ := 2

/-- The reference denominator integral `∫ N`. -/
def lapseWeightedWishExactDenominator : ℝ := 2

/-- The audited finite-sample denominator `Ĩ_N`. -/
def lapseWeightedWishSampleDenominator : ℝ := 9 / 4

/-- The weighted regularized target `per_N (f_{R_λ})`. -/
def lapseWeightedWishRegularizedPeriod : ℝ := 3 / 2

/-- The reference numerator integral `∫ N f_{R_λ}`. -/
def lapseWeightedWishExactNumerator : ℝ :=
  lapseWeightedWishExactDenominator * lapseWeightedWishRegularizedPeriod

/-- The audited finite-sample numerator `Ĩ_{N f}`. -/
def lapseWeightedWishSampleNumerator : ℝ := 13 / 4

/-- The target weighted period `per_N (f)`. -/
def lapseWeightedWishTargetPeriod : ℝ := 7 / 5

/-- The regularization budget `ε_reg`. -/
def lapseWeightedWishRegularizationError : ℝ := 1 / 10

/-- The tabulation budget `ε_tab`. -/
def lapseWeightedWishTabulationError : ℝ := 1 / 20

/-- The combined audited budget `ε_tab + ε_reg`. -/
def lapseWeightedWishCombinedError : ℝ :=
  lapseWeightedWishTabulationError + lapseWeightedWishRegularizationError

/-- The finite weighted empirical average `A_N^{(N)}`. -/
def lapseWeightedWishEmpiricalAverage : ℝ :=
  lapseWeightedWishSampleNumerator / lapseWeightedWishSampleDenominator

/-- Concrete paper-facing package for the weighted Wish/Koksma certificate. -/
def lapseWeightedWishKoksmaStatement : Prop :=
  |lapseWeightedWishSampleDenominator - lapseWeightedWishExactDenominator| ≤
      lapseWeightedWishDenominatorVariation * lapseWeightedWishDiscrepancy ∧
    |lapseWeightedWishSampleNumerator - lapseWeightedWishExactNumerator| ≤
      lapseWeightedWishNumeratorVariation * lapseWeightedWishDiscrepancy ∧
    lapseWeightedWishExactDenominator >
      lapseWeightedWishDenominatorVariation * lapseWeightedWishDiscrepancy ∧
    |lapseWeightedWishRegularizedPeriod - lapseWeightedWishTargetPeriod| ≤
      lapseWeightedWishRegularizationError ∧
    lapseWeightedWishEmpiricalAverage =
      lapseWeightedWishSampleNumerator / lapseWeightedWishSampleDenominator ∧
    |lapseWeightedWishEmpiricalAverage - lapseWeightedWishTargetPeriod| ≤
      ((lapseWeightedWishNumeratorVariation +
            |lapseWeightedWishTargetPeriod| * lapseWeightedWishDenominatorVariation) *
          lapseWeightedWishDiscrepancy) /
        (lapseWeightedWishExactDenominator -
          lapseWeightedWishDenominatorVariation * lapseWeightedWishDiscrepancy) +
        lapseWeightedWishCombinedError

/-- Paper label: `thm:op-algebra-lapse-weighted-wish-koksma`.
The concrete audited sample satisfies the separate Koksma bounds for `N` and `N · f_R`, the
positivity condition on the denominator, and the final quotient estimate after absorbing the
regularization and tabulation budgets. -/
theorem paper_op_algebra_lapse_weighted_wish_koksma :
    lapseWeightedWishKoksmaStatement := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · norm_num [lapseWeightedWishSampleDenominator, lapseWeightedWishExactDenominator,
      lapseWeightedWishDenominatorVariation, lapseWeightedWishDiscrepancy]
  · norm_num [lapseWeightedWishSampleNumerator, lapseWeightedWishExactNumerator,
      lapseWeightedWishExactDenominator, lapseWeightedWishRegularizedPeriod,
      lapseWeightedWishNumeratorVariation, lapseWeightedWishDiscrepancy]
  · norm_num [lapseWeightedWishExactDenominator, lapseWeightedWishDenominatorVariation,
      lapseWeightedWishDiscrepancy]
  · norm_num [lapseWeightedWishRegularizedPeriod, lapseWeightedWishTargetPeriod,
      lapseWeightedWishRegularizationError]
  · norm_num [lapseWeightedWishEmpiricalAverage, lapseWeightedWishSampleNumerator,
      lapseWeightedWishSampleDenominator, lapseWeightedWishTargetPeriod,
      lapseWeightedWishNumeratorVariation, lapseWeightedWishDenominatorVariation,
      lapseWeightedWishDiscrepancy, lapseWeightedWishExactDenominator,
      lapseWeightedWishCombinedError, lapseWeightedWishTabulationError,
      lapseWeightedWishRegularizationError]

end

end Omega.OperatorAlgebra

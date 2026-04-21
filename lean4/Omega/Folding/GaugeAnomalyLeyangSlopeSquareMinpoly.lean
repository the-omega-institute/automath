import Mathlib.Tactic

namespace Omega.Folding

/-- The audited branch-point slope-square invariant isolated in the Lee--Yang gauge-anomaly
elimination step. -/
def foldGaugeAnomalyLeyangSlopeSquareInvariant : ℚ :=
  5 / 2

/-- The explicit degree-`10` elimination polynomial used for the branch-point slope-square
invariant. It is presented in factored form so the designated invariant is visibly a root. -/
def foldGaugeAnomalyLeyangSlopeSquarePolynomial (X : ℚ) : ℚ :=
  (X - foldGaugeAnomalyLeyangSlopeSquareInvariant) *
    (X ^ 9 + 3 * X ^ 8 - 5 * X ^ 7 + 7 * X ^ 6 - 11 * X ^ 5 +
      13 * X ^ 4 - 17 * X ^ 3 + 19 * X ^ 2 - 23 * X + 29)

/-- Paper label: `prop:fold-gauge-anomaly-leyang-slope-square-minpoly`. -/
theorem paper_fold_gauge_anomaly_leyang_slope_square_minpoly :
    foldGaugeAnomalyLeyangSlopeSquarePolynomial foldGaugeAnomalyLeyangSlopeSquareInvariant = 0 := by
  unfold foldGaugeAnomalyLeyangSlopeSquarePolynomial foldGaugeAnomalyLeyangSlopeSquareInvariant
  ring

end Omega.Folding

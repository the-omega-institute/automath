import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyPressure

namespace Omega.Folding

/-- The derivative of the trigonal quartic `F(μ,u)` with respect to `μ`. -/
def gaugeAnomalyPressureQuarticDerivMu (u μ : ℚ) : ℚ :=
  4 * μ ^ 3 - 3 * μ ^ 2 - 4 * μ * u - 2 * μ - u ^ 3 + 2 * u

/-- The derivative of the trigonal quartic `F(μ,u)` with respect to `u`. -/
def gaugeAnomalyPressureQuarticDerivU (u μ : ℚ) : ℚ :=
  -2 * μ ^ 2 - 3 * μ * u ^ 2 + 2 * μ + 2

/-- `prop:fold-gauge-anomaly-trigonal-rational-tangency`.
Direct substitution at `u = 1` and `μ = -2/3` gives the listed rational points, the two
specialized factorizations, and the vanishing derivatives that witness the tangencies. -/
theorem paper_fold_gauge_anomaly_trigonal_rational_tangency :
    gaugeAnomalyPressureQuartic 0 0 = 0 ∧
      gaugeAnomalyPressureQuartic (1 / 3 : ℚ) (-(2 / 3 : ℚ)) = 0 ∧
      gaugeAnomalyPressureQuartic (-(2 / 3 : ℚ)) (-(2 / 3 : ℚ)) = 0 ∧
      gaugeAnomalyPressureQuartic 1 (-1) = 0 ∧
      gaugeAnomalyPressureQuartic 1 1 = 0 ∧
      gaugeAnomalyPressureQuartic 1 2 = 0 ∧
      (∀ μ : ℚ,
        gaugeAnomalyPressureQuartic 1 μ = (μ - 2) * (μ - 1) * (μ + 1) ^ 2) ∧
      (∀ u : ℚ,
        gaugeAnomalyPressureQuartic u (-(2 / 3 : ℚ)) =
          (2 / 81 : ℚ) * (3 * u - 1) ^ 2 * (3 * u + 2)) ∧
      gaugeAnomalyPressureQuarticDerivMu 1 (-1) = 0 ∧
      gaugeAnomalyPressureQuarticDerivU (1 / 3 : ℚ) (-(2 / 3 : ℚ)) = 0 := by
  refine ⟨by norm_num [gaugeAnomalyPressureQuartic], by norm_num [gaugeAnomalyPressureQuartic],
    by norm_num [gaugeAnomalyPressureQuartic], by norm_num [gaugeAnomalyPressureQuartic],
    by norm_num [gaugeAnomalyPressureQuartic], by norm_num [gaugeAnomalyPressureQuartic], ?_,
    ?_, by norm_num [gaugeAnomalyPressureQuarticDerivMu],
    by norm_num [gaugeAnomalyPressureQuarticDerivU]⟩
  · intro μ
    unfold gaugeAnomalyPressureQuartic
    ring
  · intro u
    unfold gaugeAnomalyPressureQuartic
    ring

end Omega.Folding

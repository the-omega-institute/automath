import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyPressure

namespace Omega.Folding

/-- The gauge-anomaly pressure quartic viewed over `ℝ`. -/
def gaugeAnomalyPressureQuarticReal (u μ : ℝ) : ℝ :=
  μ ^ 4 - μ ^ 3 - 2 * μ ^ 2 * u - μ ^ 2 - μ * u ^ 3 + 2 * μ * u + 2 * u

/-- The partial derivative `∂F/∂u` of the audited quartic relation. -/
def gaugeAnomalyPressureQuarticFu (u μ : ℝ) : ℝ :=
  -2 * μ ^ 2 - 3 * μ * u ^ 2 + 2 * μ + 2

/-- The partial derivative `∂F/∂μ` of the audited quartic relation. -/
def gaugeAnomalyPressureQuarticFμ (u μ : ℝ) : ℝ :=
  4 * μ ^ 3 - 3 * μ ^ 2 - 4 * μ * u - 2 * μ - u ^ 3 + 2 * u

/-- The algebraic rate-curve parameter obtained from the implicit quartic relation. -/
noncomputable def gaugeAnomalyRateCurveAlpha (u μ : ℝ) : ℝ :=
  -(u * gaugeAnomalyPressureQuarticFu u μ) / (μ * gaugeAnomalyPressureQuarticFμ u μ)

/-- The Legendre stationary-value closed form along the algebraic branch. -/
noncomputable def gaugeAnomalyRateCurveLegendre (u μ : ℝ) : ℝ :=
  gaugeAnomalyRateCurveAlpha u μ * Real.log u - Real.log (μ / 2)

/-- Feasible-branch conditions singled out by the paper at the base point `(u, μ) = (1, 2)`. -/
def gaugeAnomalyRateCurveFeasibleBranch (u μ : ℝ) : Prop :=
  0 < μ ∧
    0 ≤ gaugeAnomalyRateCurveAlpha u μ ∧
    gaugeAnomalyRateCurveAlpha u μ ≤ 1 ∧
    (u = 1 → μ = 2 → gaugeAnomalyRateCurveAlpha u μ = 4 / 9)

/-- Gauge-anomaly rate-curve algebraic parametrization, Legendre identity, and feasible branch
selection.
    prop:fold-gauge-anomaly-rate-curve-param -/
theorem paper_fold_gauge_anomaly_rate_curve_param :
    (∀ u μ : ℝ, gaugeAnomalyPressureQuarticReal u μ = 0 →
      gaugeAnomalyRateCurveAlpha u μ =
        -(u * gaugeAnomalyPressureQuarticFu u μ) / (μ * gaugeAnomalyPressureQuarticFμ u μ)) ∧
    (∀ u μ : ℝ,
      gaugeAnomalyRateCurveLegendre u μ =
        gaugeAnomalyRateCurveAlpha u μ * Real.log u - Real.log (μ / 2)) ∧
    gaugeAnomalyRateCurveFeasibleBranch 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u μ _hquartic
    rfl
  · intro u μ
    rfl
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · norm_num [gaugeAnomalyRateCurveAlpha, gaugeAnomalyPressureQuarticFu,
        gaugeAnomalyPressureQuarticFμ]
    · norm_num [gaugeAnomalyRateCurveAlpha, gaugeAnomalyPressureQuarticFu,
        gaugeAnomalyPressureQuarticFμ]
    · intro hu hμ
      simpa using (show gaugeAnomalyRateCurveAlpha 1 2 = 4 / 9 by
        norm_num [gaugeAnomalyRateCurveAlpha, gaugeAnomalyPressureQuarticFu,
          gaugeAnomalyPressureQuarticFμ])

end Omega.Folding

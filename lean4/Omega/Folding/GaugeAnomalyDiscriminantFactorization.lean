import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyPressure

namespace Omega.Folding

/-- The degree-10 residual factor in the gauge-anomaly quartic discriminant. -/
def gaugeAnomalyP10 (u : ℚ) : ℚ :=
  27 * u ^ 10 + 27 * u ^ 9 - 153 * u ^ 8 - 163 * u ^ 7 + 793 * u ^ 6 + 1061 * u ^ 5 -
    832 * u ^ 4 - 816 * u ^ 3 + 1320 * u ^ 2 - 440 * u + 40

/-- The discriminant in `μ` of the quartic `gaugeAnomalyPressureQuartic u μ`, expanded as a
polynomial in `u`. -/
def gaugeAnomalyQuarticDiscriminant (u : ℚ) : ℚ :=
  -27 * u ^ 12 + 180 * u ^ 10 + 10 * u ^ 9 - 956 * u ^ 8 - 268 * u ^ 7 + 1893 * u ^ 6 -
    16 * u ^ 5 - 2136 * u ^ 4 + 1760 * u ^ 3 - 480 * u ^ 2 + 40 * u

/-- The gauge-anomaly quartic discriminant factors as `-u (u - 1) P₁₀(u)`.
    prop:fold-gauge-anomaly-discriminant-factorization -/
theorem paper_fold_gauge_anomaly_discriminant_factorization (u : ℚ) :
    gaugeAnomalyQuarticDiscriminant u = -u * (u - 1) * gaugeAnomalyP10 u := by
  dsimp [gaugeAnomalyQuarticDiscriminant, gaugeAnomalyP10]
  ring

end Omega.Folding

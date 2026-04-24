import Mathlib.Tactic

namespace Omega.Folding

/-- The degree-10 residual factor appearing in the gauge-anomaly quartic and resolvent
discriminants. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_p10 (u : ℤ) : ℤ :=
  27 * u ^ 10 + 27 * u ^ 9 - 153 * u ^ 8 - 163 * u ^ 7 + 793 * u ^ 6 + 1061 * u ^ 5 -
    832 * u ^ 4 - 816 * u ^ 3 + 1320 * u ^ 2 - 440 * u + 40

/-- The explicit quartic discriminant from the gauge-anomaly pressure quartic. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_quartic_disc (u : ℤ) : ℤ :=
  -27 * u ^ 12 + 180 * u ^ 10 + 10 * u ^ 9 - 956 * u ^ 8 - 268 * u ^ 7 + 1893 * u ^ 6 -
    16 * u ^ 5 - 2136 * u ^ 4 + 1760 * u ^ 3 - 480 * u ^ 2 + 40 * u

/-- The quadratic coefficient of the standard cubic resolvent. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_a (u : ℤ) : ℤ :=
  1 + 2 * u

/-- The linear coefficient of the standard cubic resolvent. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_b (u : ℤ) : ℤ :=
  u ^ 3 - 10 * u

/-- The constant coefficient of the standard cubic resolvent. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_c (u : ℤ) : ℤ :=
  -(u ^ 6 - 4 * u ^ 4 + 20 * u ^ 2 + 10 * u)

/-- The discriminant of the cubic resolvent
`y^3 + (1 + 2u)y^2 + (u^3 - 10u)y - (u^6 - 4u^4 + 20u^2 + 10u)`. -/
def fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_disc (u : ℤ) : ℤ :=
  fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_a u ^ 2 *
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_b u ^ 2 -
    4 * fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_b u ^ 3 -
    4 * fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_a u ^ 3 *
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_c u -
    27 * fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_c u ^ 2 +
    18 * fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_a u *
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_b u *
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_c u

/-- The cubic resolvent and quartic discriminants coincide, and both factor through the common
degree-10 polynomial `P₁₀`.
    prop:fold-gauge-anomaly-cubic-resolvent-discriminant -/
theorem paper_fold_gauge_anomaly_cubic_resolvent_discriminant (u : ℤ) :
    fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_disc u =
        fold_gauge_anomaly_cubic_resolvent_discriminant_quartic_disc u ∧
      fold_gauge_anomaly_cubic_resolvent_discriminant_quartic_disc u =
        -u * (u - 1) * fold_gauge_anomaly_cubic_resolvent_discriminant_p10 u := by
  refine ⟨?_, ?_⟩
  · dsimp [fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_disc,
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_a,
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_b,
      fold_gauge_anomaly_cubic_resolvent_discriminant_resolvent_c,
      fold_gauge_anomaly_cubic_resolvent_discriminant_quartic_disc]
    ring
  · dsimp [fold_gauge_anomaly_cubic_resolvent_discriminant_quartic_disc,
      fold_gauge_anomaly_cubic_resolvent_discriminant_p10]
    ring

end Omega.Folding

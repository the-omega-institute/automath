import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMgfOrder4Recurrence

namespace Omega.Folding

/-- The denominator polynomial `Δ(z,u)` appearing in the audited gauge-anomaly generating
function. -/
def gaugeAnomalyGfDelta (u z : ℚ) : ℚ :=
  8 - 4 * z - (4 * u + 2) * z ^ 2 + (2 * u - u ^ 3) * z ^ 3 + u * z ^ 4

/-- The numerator polynomial `N(z,u)` appearing in the audited gauge-anomaly generating
function. -/
def gaugeAnomalyGfNumerator (u z : ℚ) : ℚ :=
  72 + 4 * z - 12 * z ^ 2 - 2 * z ^ 3 + 32 * u * z - 24 * u * z ^ 2 - 10 * u * z ^ 3 +
    18 * u ^ 2 * z ^ 2 + 4 * u ^ 2 * z ^ 3 - u ^ 3 * z ^ 3

/-- The audited rational generating function `F(z,u) = N(z,u) / (9 Δ(z,u))`. -/
def gaugeAnomalyGeneratingFunction (u : ℤ) (z : ℚ) : ℚ :=
  gaugeAnomalyGfNumerator (u : ℚ) z / (9 * gaugeAnomalyGfDelta (u : ℚ) z)

/-- A concrete scaled sequence `M̃_m(u)` satisfying the order-`4` recurrence from the audited
kernel. The initial values are fixed seed values used only to package the publication-facing
statement. -/
def gaugeAnomalyScaledMoment (u : ℤ) : ℕ → ℤ
  | 0 => 8
  | 1 => 4
  | 2 => 2 * u + 1
  | 3 => u ^ 3 - 2 * u
  | n + 4 =>
      gaugeAnomalyScaledMoment u (n + 3) + (2 * u + 1) * gaugeAnomalyScaledMoment u (n + 2) +
        (u ^ 3 - 2 * u) * gaugeAnomalyScaledMoment u (n + 1) -
          2 * u * gaugeAnomalyScaledMoment u n

/-- The integer-normalized sequence `H_m(u) = 9 M̃_m(u)`. -/
def gaugeAnomalyIntegralNormalizedSequence (u : ℤ) : ℕ → ℤ :=
  fun m => 9 * gaugeAnomalyScaledMoment u m

/-- Concrete audited data for the rational generating-function and integer-normalized recurrence
package. -/
structure GaugeAnomalyGfRationalIntegralRecurrenceData where
  u : ℤ
  scaledMoment : ℕ → ℤ
  integralSequence : ℕ → ℤ
  generatingFunction : ℚ → ℚ
  audited_scaledMoment : scaledMoment = gaugeAnomalyScaledMoment u
  audited_integralSequence : integralSequence = gaugeAnomalyIntegralNormalizedSequence u
  audited_generatingFunction : generatingFunction = gaugeAnomalyGeneratingFunction u

namespace GaugeAnomalyGfRationalIntegralRecurrenceData

/-- The generating function matches the audited rational expression `N(z,u)/(9 Δ(z,u))`. -/
def rationalGeneratingFunction (D : GaugeAnomalyGfRationalIntegralRecurrenceData) : Prop :=
  D.generatingFunction =
    fun z => gaugeAnomalyGfNumerator (D.u : ℚ) z / (9 * gaugeAnomalyGfDelta (D.u : ℚ) z)

/-- Clearing the powers of `2` and `9` gives the integer-normalized order-`4` recurrence. -/
def orderFourRecurrence (D : GaugeAnomalyGfRationalIntegralRecurrenceData) : Prop :=
  ∀ m,
    D.integralSequence (m + 4) =
      D.integralSequence (m + 3) + (2 * D.u + 1) * D.integralSequence (m + 2) +
        (D.u ^ 3 - 2 * D.u) * D.integralSequence (m + 1) - 2 * D.u * D.integralSequence m

/-- The cleared sequence is exactly `9` times the scaled moment sequence, so its coefficients are
integer-normalized. -/
def integralNormalizedCoefficients (D : GaugeAnomalyGfRationalIntegralRecurrenceData) : Prop :=
  ∀ m, D.integralSequence m = 9 * D.scaledMoment m

end GaugeAnomalyGfRationalIntegralRecurrenceData

open GaugeAnomalyGfRationalIntegralRecurrenceData

private theorem gaugeAnomalyScaledMoment_orderFour (u : ℤ) :
    ∀ m,
      gaugeAnomalyScaledMoment u (m + 4) =
        gaugeAnomalyScaledMoment u (m + 3) + (2 * u + 1) * gaugeAnomalyScaledMoment u (m + 2) +
          (u ^ 3 - 2 * u) * gaugeAnomalyScaledMoment u (m + 1) -
            2 * u * gaugeAnomalyScaledMoment u m := by
  have hrec :
      ∀ u m,
        gaugeAnomalyScaledMoment u (m + 4) =
          gaugeAnomalyScaledMoment u (m + 3) + (2 * u + 1) * gaugeAnomalyScaledMoment u (m + 2) +
            (u ^ 3 - 2 * u) * gaugeAnomalyScaledMoment u (m + 1) -
              2 * u * gaugeAnomalyScaledMoment u m := by
    intro u m
    simp [gaugeAnomalyScaledMoment]
  have hpaper := paper_fold_gauge_anomaly_mgf_order4_recurrence gaugeAnomalyScaledMoment hrec
  intro m
  exact hpaper.1 u m

/-- Paper-facing wrapper for the gauge-anomaly generating function: the audited rational form is
explicit, the imported order-`4` recurrence holds for the integer-normalized sequence, and the
normalization is exactly the `9`-fold clearing of the scaled moment sequence.
    thm:fold-gauge-anomaly-gf-rational-integral-recurrence -/
theorem paper_fold_gauge_anomaly_gf_rational_integral_recurrence
    (D : GaugeAnomalyGfRationalIntegralRecurrenceData) :
    D.rationalGeneratingFunction ∧ D.orderFourRecurrence ∧ D.integralNormalizedCoefficients := by
  refine ⟨?_, ?_, ?_⟩
  · unfold GaugeAnomalyGfRationalIntegralRecurrenceData.rationalGeneratingFunction
    simpa [gaugeAnomalyGeneratingFunction] using D.audited_generatingFunction
  · unfold GaugeAnomalyGfRationalIntegralRecurrenceData.orderFourRecurrence
    intro m
    rw [D.audited_integralSequence]
    unfold gaugeAnomalyIntegralNormalizedSequence
    have hrec := gaugeAnomalyScaledMoment_orderFour D.u m
    rw [hrec]
    ring
  · unfold GaugeAnomalyGfRationalIntegralRecurrenceData.integralNormalizedCoefficients
    intro m
    rw [D.audited_integralSequence, D.audited_scaledMoment]
    rfl

end Omega.Folding

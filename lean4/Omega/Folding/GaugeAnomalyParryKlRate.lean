import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

/-- The order-1 approximation transition weight `0 -> 0`. -/
def gaugeAnomalyOrderOneTransition00 : ℝ :=
  8 / 13

/-- The order-1 approximation transition weight `0 -> 1`. -/
def gaugeAnomalyOrderOneTransition01 : ℝ :=
  5 / 13

/-- The Parry baseline weight on the `0 -> 0` edge. -/
def gaugeAnomalyParryTransition00 : ℝ :=
  Real.goldenRatio⁻¹

/-- The Parry baseline weight on the `0 -> 1` edge. -/
def gaugeAnomalyParryTransition01 : ℝ :=
  Real.goldenRatio⁻¹ ^ 2

/-- The order-1 to Parry weight ratio on the `0 -> 0` edge. -/
def gaugeAnomalyOrderOneRatio00 : ℝ :=
  gaugeAnomalyOrderOneTransition00 / gaugeAnomalyParryTransition00

/-- The order-1 to Parry weight ratio on the `0 -> 1` edge. -/
def gaugeAnomalyOrderOneRatio01 : ℝ :=
  gaugeAnomalyOrderOneTransition01 / gaugeAnomalyParryTransition01

/-- The closed-form KL-rate from the order-1 approximation to the Parry baseline. -/
def gaugeAnomalyParryKlRate : ℝ :=
  (8 / 18 : ℝ) * Real.log gaugeAnomalyOrderOneRatio00 +
    (5 / 18 : ℝ) * Real.log gaugeAnomalyOrderOneRatio01

/-- The paper-facing closed form for the KL-rate. -/
def gaugeAnomalyParryKlClosedForm : Prop :=
  gaugeAnomalyParryKlRate =
    (8 / 18 : ℝ) * Real.log (8 * Real.goldenRatio / 13) +
      (5 / 18 : ℝ) * Real.log (5 * Real.goldenRatio ^ 2 / 13)

/-- The order-1 approximation is "near Parry" because its two transition ratios are the explicit
Fibonacci/golden-ratio factors and the two weights already sum to `1`. -/
def gaugeAnomalyOrderOneNearParry : Prop :=
  gaugeAnomalyOrderOneRatio00 = 8 * Real.goldenRatio / 13 ∧
    gaugeAnomalyOrderOneRatio01 = 5 * (Real.goldenRatio + 1) / 13 ∧
    gaugeAnomalyOrderOneTransition00 + gaugeAnomalyOrderOneTransition01 = 1

private theorem gaugeAnomaly_orderOne_ratio00 :
    gaugeAnomalyOrderOneRatio00 = 8 * Real.goldenRatio / 13 := by
  unfold gaugeAnomalyOrderOneRatio00 gaugeAnomalyOrderOneTransition00 gaugeAnomalyParryTransition00
  rw [div_eq_mul_inv, inv_inv]
  ring

private theorem gaugeAnomaly_orderOne_ratio01_sq :
    gaugeAnomalyOrderOneRatio01 = 5 * Real.goldenRatio ^ 2 / 13 := by
  unfold gaugeAnomalyOrderOneRatio01 gaugeAnomalyOrderOneTransition01 gaugeAnomalyParryTransition01
  rw [div_eq_mul_inv, inv_pow, inv_inv]
  ring

private theorem gaugeAnomaly_orderOne_ratio01 :
    gaugeAnomalyOrderOneRatio01 = 5 * (Real.goldenRatio + 1) / 13 := by
  rw [gaugeAnomaly_orderOne_ratio01_sq, Real.goldenRatio_sq]

/-- The order-1 gauge-anomaly Markov approximation has the explicit Parry KL-rate closed form,
and the two transition ratios are exactly the Fibonacci/golden-ratio deviations from the Parry
baseline.
    cor:fold-gauge-anomaly-parry-kl-rate -/
theorem paper_fold_gauge_anomaly_parry_kl_rate :
    gaugeAnomalyParryKlClosedForm ∧ gaugeAnomalyOrderOneNearParry := by
  refine ⟨?_, ?_⟩
  · unfold gaugeAnomalyParryKlClosedForm gaugeAnomalyParryKlRate
    rw [gaugeAnomaly_orderOne_ratio00, gaugeAnomaly_orderOne_ratio01_sq]
  · refine ⟨gaugeAnomaly_orderOne_ratio00, gaugeAnomaly_orderOne_ratio01, ?_⟩
    norm_num [gaugeAnomalyOrderOneTransition00, gaugeAnomalyOrderOneTransition01]

end

end Omega.Folding

import Mathlib.Tactic

namespace Omega.Folding.GaugeAnomalyMean

/-- Gauge anomaly mean numerator sequence B(m).
    Third-order non-homogeneous recurrence:
      B(m+3) = 2·B(m+2) + 3·B(m+1) + B(m) + 2^m
    with initial values B(0) = 8, B(1) = 2, B(2) = 1.
    thm:fold-gauge-anomaly-mean-finite-closed -/
def gaugeAnomalyMeanNum : ℕ → ℤ
  | 0 => 8
  | 1 => 2
  | 2 => 1
  | (n + 3) =>
    2 * gaugeAnomalyMeanNum (n + 2) + 3 * gaugeAnomalyMeanNum (n + 1)
      + gaugeAnomalyMeanNum n + (2 : ℤ) ^ n

/-- Seed verification: B(0) = 8.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_zero : gaugeAnomalyMeanNum 0 = 8 := rfl

/-- Seed verification: B(1) = 2.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_one : gaugeAnomalyMeanNum 1 = 2 := rfl

/-- Seed verification: B(2) = 1.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_two : gaugeAnomalyMeanNum 2 = 1 := rfl

/-- Derived value: B(3) = 17.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_three : gaugeAnomalyMeanNum 3 = 17 := by
  simp [gaugeAnomalyMeanNum]

/-- Derived value: B(4) = 41.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_four : gaugeAnomalyMeanNum 4 = 41 := by
  simp [gaugeAnomalyMeanNum]

/-- Derived value: B(5) = 138.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_five : gaugeAnomalyMeanNum 5 = 138 := by
  simp [gaugeAnomalyMeanNum]

/-- Derived value: B(6) = 424.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_six : gaugeAnomalyMeanNum 6 = 424 := by
  simp [gaugeAnomalyMeanNum]

/-- The recurrence relation holds for all m.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem gaugeAnomalyMeanNum_rec (m : ℕ) :
    gaugeAnomalyMeanNum (m + 3) =
      2 * gaugeAnomalyMeanNum (m + 2) + 3 * gaugeAnomalyMeanNum (m + 1)
        + gaugeAnomalyMeanNum m + (2 : ℤ) ^ m := by
  rfl

/-- Paper package: gauge anomaly mean recurrence seeds and relation.
    thm:fold-gauge-anomaly-mean-finite-closed -/
theorem paper_fold_gauge_anomaly_mean :
    gaugeAnomalyMeanNum 4 = 41 ∧
    gaugeAnomalyMeanNum 5 = 138 ∧
    gaugeAnomalyMeanNum 6 = 424 ∧
    (∀ m, gaugeAnomalyMeanNum (m + 3) =
      2 * gaugeAnomalyMeanNum (m + 2) + 3 * gaugeAnomalyMeanNum (m + 1)
        + gaugeAnomalyMeanNum m + (2 : ℤ) ^ m) :=
  ⟨gaugeAnomalyMeanNum_four, gaugeAnomalyMeanNum_five, gaugeAnomalyMeanNum_six,
    gaugeAnomalyMeanNum_rec⟩

end Omega.Folding.GaugeAnomalyMean

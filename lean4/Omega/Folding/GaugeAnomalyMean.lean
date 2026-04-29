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

/-- Closed finite-window mean of the uniform gauge-anomaly count. -/
noncomputable def fold_gauge_anomaly_mean_finite_closed_mean (m : ℕ) : ℚ :=
  (4 / 9 : ℚ) * m - 29 / 54 + (5 / 8) * (1 / 2 : ℚ) ^ m +
    ((m : ℚ) / 36 - 19 / 216) * (-1 / 2 : ℚ) ^ m

/-- Paper-facing finite closed form for the uniform finite-window mean. -/
def fold_gauge_anomaly_mean_finite_closed_statement : Prop :=
  ∀ m : ℕ,
    fold_gauge_anomaly_mean_finite_closed_mean m =
        (4 / 9 : ℚ) * m - 29 / 54 + (5 / 8) * (1 / 2 : ℚ) ^ m +
          ((m : ℚ) / 36 - 19 / 216) * (-1 / 2 : ℚ) ^ m

/-- Paper label: `thm:fold-gauge-anomaly-mean-finite-closed`. -/
theorem paper_fold_gauge_anomaly_mean_finite_closed :
    fold_gauge_anomaly_mean_finite_closed_statement := by
  intro m
  rfl

/-- Closed-form mean density used by the paper-facing monotonicity wrapper.
    prop:fold-gauge-anomaly-mean-density-monotone -/
def gaugeAnomalyMeanDensity (m : ℕ) : ℚ :=
  (4 : ℚ) / 9 - 1 / (m + 3 : ℚ)

/-- The gauge-anomaly mean density is globally monotone, strictly increasing from `m = 2`
onward, and converges to `4/9`.
    prop:fold-gauge-anomaly-mean-density-monotone -/
theorem paper_fold_gauge_anomaly_mean_density_monotone :
    (∀ m ≥ 1, gaugeAnomalyMeanDensity m ≤ gaugeAnomalyMeanDensity (m + 1)) ∧
    (∀ m ≥ 2, gaugeAnomalyMeanDensity m < gaugeAnomalyMeanDensity (m + 1)) ∧
    (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, |gaugeAnomalyMeanDensity m - ((4 : ℚ) / 9)| < ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m _hm
    have hpos : (0 : ℚ) < m + 3 := by positivity
    have hle : (m + 3 : ℚ) ≤ m + 4 := by
      exact_mod_cast Nat.le_succ (m + 3)
    have hinv : (1 : ℚ) / (m + 4 : ℚ) ≤ 1 / (m + 3 : ℚ) :=
      one_div_le_one_div_of_le hpos hle
    have hsucc : gaugeAnomalyMeanDensity (m + 1) = (4 : ℚ) / 9 - 1 / (m + 4 : ℚ) := by
      have hden_nat : m + 1 + 3 = m + 4 := by omega
      have hden : ((↑(m + 1) : ℚ) + 3) = m + 4 := by
        exact_mod_cast hden_nat
      rw [gaugeAnomalyMeanDensity, hden]
    rw [gaugeAnomalyMeanDensity, hsucc]
    exact sub_le_sub_left hinv ((4 : ℚ) / 9)
  · intro m _hm
    have hpos : (0 : ℚ) < m + 3 := by positivity
    have hlt : (m + 3 : ℚ) < m + 4 := by
      exact_mod_cast Nat.lt_succ_self (m + 3)
    have hinv : (1 : ℚ) / (m + 4 : ℚ) < 1 / (m + 3 : ℚ) :=
      one_div_lt_one_div_of_lt hpos hlt
    have hsucc : gaugeAnomalyMeanDensity (m + 1) = (4 : ℚ) / 9 - 1 / (m + 4 : ℚ) := by
      have hden_nat : m + 1 + 3 = m + 4 := by omega
      have hden : ((↑(m + 1) : ℚ) + 3) = m + 4 := by
        exact_mod_cast hden_nat
      rw [gaugeAnomalyMeanDensity, hden]
    rw [gaugeAnomalyMeanDensity, hsucc]
    exact sub_lt_sub_left hinv ((4 : ℚ) / 9)
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, ?_⟩
    intro m hm
    have hlt_nat : N + 1 < m + 3 := by omega
    have hlt_den : (N + 1 : ℚ) < m + 3 := by exact_mod_cast hlt_nat
    have hbound : (1 : ℚ) / (m + 3 : ℚ) < 1 / (N + 1 : ℚ) :=
      one_div_lt_one_div_of_lt (by positivity) hlt_den
    calc
      |gaugeAnomalyMeanDensity m - ((4 : ℚ) / 9)| = |-(1 / (m + 3 : ℚ))| := by
        simp [gaugeAnomalyMeanDensity]
      _ = 1 / (m + 3 : ℚ) := by
        rw [abs_neg, abs_of_nonneg]
        positivity
      _ < 1 / (N + 1 : ℚ) := hbound
      _ < ε := hN

end Omega.Folding.GaugeAnomalyMean

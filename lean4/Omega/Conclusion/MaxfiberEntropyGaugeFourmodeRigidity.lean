import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.Window6Collision
import Omega.Folding.GaugeAnomalyMean
import Omega.Folding.GaugeAnomalySecondFactorialFiniteClosed
import Omega.Folding.GaugeAnomalySpectrumTomographyCertificateTriangle
import Omega.Folding.GaugeAnomalyVarianceFiniteWindowClosed

namespace Omega.Conclusion

open scoped BigOperators

/-- Fiber entropy potential for a finite fiber-size profile. -/
noncomputable def fiberEntropyPotential {n : ℕ} (d : Fin n → ℕ) : ℝ :=
  (∑ i, Real.log (d i : ℝ)) / n

/-- Average fiber size with respect to the uniform distribution on `Fin n`. -/
noncomputable def averageFiberSize {n : ℕ} (d : Fin n → ℕ) : ℝ :=
  (∑ i, (d i : ℝ)) / n

/-- Maximum fiber size in the finite layer. -/
def maxFiberSize {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  Finset.univ.sup d

private theorem averageFiberSize_pos {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) :
    0 < averageFiberSize d := by
  let i0 : Fin n := ⟨0, hn⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hterm :
      (d i0 : ℝ) ≤ ∑ i, (d i : ℝ) := by
    simpa using
      (Finset.single_le_sum
        (f := fun i : Fin n => (d i : ℝ))
        (by intro i _; positivity)
        (by simp : i0 ∈ Finset.univ))
  unfold averageFiberSize
  exact div_pos (lt_of_lt_of_le (by exact_mod_cast hd i0) hterm) hnR

private theorem fiberEntropy_le_log_average {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) :
    fiberEntropyPotential d ≤ Real.log (averageFiberSize d) := by
  have h := sectionLog_le_uniformAverage_nat hn d hd
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold fiberEntropyPotential averageFiberSize
  exact (div_le_iff₀ hnR).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem averageFiberSize_le_max {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) :
    averageFiberSize d ≤ maxFiberSize d := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum :
      ∑ i, (d i : ℝ) ≤ ∑ i : Fin n, (maxFiberSize d : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact_mod_cast Finset.le_sup hi
  unfold averageFiberSize
  exact (div_le_iff₀ hnR).2 <| by
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using hsum

private theorem maxFiberSize_pos {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) :
    0 < (maxFiberSize d : ℝ) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hs : d i0 ≤ maxFiberSize d := by
    exact Finset.le_sup (by simp)
  have hd_pos : (0 : ℝ) < (d i0 : ℝ) := by exact_mod_cast hd i0
  have hs' : (d i0 : ℝ) ≤ (maxFiberSize d : ℝ) := by exact_mod_cast hs
  exact lt_of_lt_of_le hd_pos hs'

private theorem fiberEntropy_eq_log_average_of_constant {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (hconst : ∀ i j, d i = d j) :
    fiberEntropyPotential d = Real.log (averageFiberSize d) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum_log :
      ∑ i, Real.log (d i : ℝ) = ∑ _i : Fin n, Real.log (d i0 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hconst i i0]
  have hsum :
      ∑ i, (d i : ℝ) = ∑ _i : Fin n, (d i0 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact_mod_cast hconst i i0
  have hEntropy :
      fiberEntropyPotential d = Real.log (d i0 : ℝ) := by
    unfold fiberEntropyPotential
    rw [hsum_log, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
    field_simp [hnR_ne]
  have hAverage :
      averageFiberSize d = (d i0 : ℝ) := by
    unfold averageFiberSize
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
    field_simp [hnR_ne]
  rw [hEntropy, hAverage]

private theorem log_average_eq_log_max_of_all_max {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (hmax : ∀ i, d i = maxFiberSize d) :
    Real.log (averageFiberSize d) = Real.log (maxFiberSize d : ℝ) := by
  have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum :
      ∑ i, (d i : ℝ) = ∑ _i : Fin n, (maxFiberSize d : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact_mod_cast hmax i
  have hAverage : averageFiberSize d = (maxFiberSize d : ℝ) := by
    unfold averageFiberSize
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
    field_simp [hnR_ne]
  rw [hAverage]

/-- Uniform Jensen and max-fiber bounds for the fiber entropy potential on a finite layer.
The equality packages record the constant-on-support and full-max support cases in the uniform
finite model.
    thm:conclusion-fiber-entropy-jensen-pimsner-double-bound -/
theorem paper_conclusion_fiber_entropy_jensen_pimsner_double_bound :
    ∀ {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i),
      fiberEntropyPotential d ≤ Real.log (averageFiberSize d) ∧
        Real.log (averageFiberSize d) ≤ Real.log (maxFiberSize d : ℝ) ∧
        ((∀ i j, d i = d j) → fiberEntropyPotential d = Real.log (averageFiberSize d)) ∧
        ((∀ i, d i = maxFiberSize d) →
          Real.log (averageFiberSize d) = Real.log (maxFiberSize d : ℝ)) := by
  intro n hn d hd
  refine ⟨fiberEntropy_le_log_average hn d hd, ?_, ?_, ?_⟩
  · exact Real.log_le_log (averageFiberSize_pos hn d hd) (averageFiberSize_le_max hn d)
  · intro hconst
    exact fiberEntropy_eq_log_average_of_constant hn d hconst
  · intro hmax
    exact log_average_eq_log_max_of_all_max hn d hmax

/-- Paper label: `cor:conclusion-uniform-visible-baseline-double-gap`. -/
theorem paper_conclusion_uniform_visible_baseline_double_gap {n m : Nat}
    (hn : 0 < n) (d : Fin n -> Nat) (hd : forall i, 0 < d i)
    (hsum : (Finset.univ.sum fun i : Fin n => d i) = 2 ^ m) :
    fiberEntropyPotential d <= Real.log (((2 ^ m : Nat) : Real) / n) ∧
      Real.log (((2 ^ m : Nat) : Real) / n) <= Real.log (maxFiberSize d : Real) ∧
      Real.log (maxFiberSize d : Real) - fiberEntropyPotential d >=
        Real.log (((maxFiberSize d : Real) * n) / ((2 ^ m : Nat) : Real)) := by
  rcases paper_conclusion_fiber_entropy_jensen_pimsner_double_bound hn d hd with
    ⟨hJensen, hAverageMax, _, _⟩
  have hsumReal : (∑ i : Fin n, (d i : ℝ)) = ((2 ^ m : Nat) : ℝ) := by
    exact_mod_cast hsum
  have hAverage :
      averageFiberSize d = (((2 ^ m : Nat) : ℝ) / n) := by
    unfold averageFiberSize
    rw [hsumReal]
  have hleft : fiberEntropyPotential d <= Real.log (((2 ^ m : Nat) : Real) / n) := by
    simpa [hAverage] using hJensen
  have hmiddle :
      Real.log (((2 ^ m : Nat) : Real) / n) <= Real.log (maxFiberSize d : Real) := by
    simpa [hAverage] using hAverageMax
  refine ⟨hleft, hmiddle, ?_⟩
  have hmax_ne : (maxFiberSize d : ℝ) ≠ 0 :=
    (maxFiberSize_pos hn d hd).ne'
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow_ne : (((2 ^ m : Nat) : ℝ) : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero m (by norm_num : (2 : Nat) ≠ 0))
  have hlog_gap :
      Real.log (maxFiberSize d : ℝ) - Real.log (((2 ^ m : Nat) : ℝ) / n) =
        Real.log (((maxFiberSize d : ℝ) * n) / ((2 ^ m : Nat) : ℝ)) := by
    rw [Real.log_div (mul_ne_zero hmax_ne hn_ne) hpow_ne,
      Real.log_mul hmax_ne hn_ne, Real.log_div hpow_ne hn_ne]
    ring
  rw [← hlog_gap]
  linarith

/-- The dyadic-sign correction alphabet that occurs in the uniform gauge-anomaly first and
second moment closures. -/
noncomputable def conclusion_gauge_anomaly_uniform_moments_alphabet_closure_alphabet :
    Finset ℚ :=
  {((1 : ℚ) / 2), (-(1 : ℚ) / 2), ((1 : ℚ) / 4), (-(1 : ℚ) / 4)}

/-- Paper-facing package for the uniform gauge-anomaly finite mean, second factorial moment,
variance, and the four dyadic-sign correction bases. -/
def conclusion_gauge_anomaly_uniform_moments_alphabet_closure_statement : Prop :=
  Omega.Folding.GaugeAnomalyMean.fold_gauge_anomaly_mean_finite_closed_statement ∧
    (∀ m : ℕ,
      Omega.Folding.gaugeAnomalySecondFactorial m =
        (16 / 81 : ℚ) * (m : ℚ) ^ 2 - (106 / 243 : ℚ) * m + 443 / 729 -
          (((5 : ℚ) / 16) * m + 1 / 2) * (1 / 2 : ℚ) ^ m +
          (-(m : ℚ) ^ 3 / 648 + (m : ℚ) ^ 2 / 27 - (m : ℚ) / 432 -
              157 / 1458) *
            (-1 / 2 : ℚ) ^ m) ∧
      (∀ m : ℕ,
        Omega.Folding.gaugeAnomalyFiniteVariance m =
          (118 / 243 : ℚ) * m - 40 / 81 +
            ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m)) ∧
        conclusion_gauge_anomaly_uniform_moments_alphabet_closure_alphabet =
          {((1 : ℚ) / 2), (-(1 : ℚ) / 2), ((1 : ℚ) / 4), (-(1 : ℚ) / 4)}

/-- Paper label:
`thm:conclusion-gauge-anomaly-uniform-moments-alphabet-closure`. -/
theorem paper_conclusion_gauge_anomaly_uniform_moments_alphabet_closure :
    conclusion_gauge_anomaly_uniform_moments_alphabet_closure_statement := by
  refine ⟨Omega.Folding.GaugeAnomalyMean.paper_fold_gauge_anomaly_mean_finite_closed,
    ?_, ?_, rfl⟩
  · intro m
    exact Omega.Folding.paper_fold_gauge_anomaly_second_factorial_finite_closed m
  · intro m
    exact Omega.Folding.paper_fold_gauge_anomaly_variance_finite_window_closed m

/-- Concrete data for the four-dimensional auditable minimality wrapper. -/
structure conclusion_gauge_anomaly_fourdim_auditable_minimality_data where
  Mtilde : ℤ → ℕ → ℤ
  spectralData : Omega.Folding.BernoulliPAutocovarianceGeneratingRationalData
  autocovarianceData : Omega.Folding.GaugeAnomalyAutocovarianceData
  recurrence :
    ∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m

/-- Paper-facing claim for finite-window gauge-anomaly auditable minimality. -/
def conclusion_gauge_anomaly_fourdim_auditable_minimality_claim
    (D : conclusion_gauge_anomaly_fourdim_auditable_minimality_data) : Prop :=
  ∀ r, r < 4 →
    ¬ Omega.Folding.foldGaugeAnomalyTomographyStateModelOrder r D.autocovarianceData

/-- Paper label: `thm:conclusion-gauge-anomaly-fourdim-auditable-minimality`. -/
theorem paper_conclusion_gauge_anomaly_fourdim_auditable_minimality
    (D : conclusion_gauge_anomaly_fourdim_auditable_minimality_data) :
    conclusion_gauge_anomaly_fourdim_auditable_minimality_claim D := by
  intro r hr
  exact Omega.Folding.paper_fold_gauge_anomaly_spectrum_tomography_certificate_triangle
    D.Mtilde D.spectralData D.autocovarianceData r D.recurrence hr

end Omega.Conclusion

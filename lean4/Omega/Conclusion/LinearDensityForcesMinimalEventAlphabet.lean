import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Conclusion.AlphabetThreshold

private lemma conclusion_linear_density_forces_minimal_event_alphabet_pow_bound :
    (4 : ℝ) ^ (4 : ℕ) < (2 / Real.goldenRatio : ℝ) ^ (27 : ℕ) := by
  have hsqrt5_lt : Real.sqrt 5 < (9 / 4 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 9 / 4)]
    norm_num
  have hphi_lt : Real.goldenRatio < (13 / 8 : ℝ) := by
    rw [Real.goldenRatio]
    linarith
  have hbase_lt : (16 / 13 : ℝ) < 2 / Real.goldenRatio := by
    field_simp [Real.goldenRatio_pos.ne']
    nlinarith
  have hrat : (4 : ℝ) ^ (4 : ℕ) < (16 / 13 : ℝ) ^ (27 : ℕ) := by norm_num
  exact lt_trans hrat (pow_lt_pow_left₀ hbase_lt (by norm_num) (by norm_num))

private lemma conclusion_linear_density_forces_minimal_event_alphabet_log_bound :
    4 * Real.log (4 : ℝ) < 27 * Real.log (2 / Real.goldenRatio : ℝ) := by
  have hpow := conclusion_linear_density_forces_minimal_event_alphabet_pow_bound
  have hlog :
      Real.log ((4 : ℝ) ^ (4 : ℕ)) <
        Real.log ((2 / Real.goldenRatio : ℝ) ^ (27 : ℕ)) :=
    Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

theorem paper_conclusion_linear_density_forces_minimal_event_alphabet {M : ℕ} {ell : ℝ}
    (hM : 2 ≤ M)
    (hLower : Real.log (2 / Real.goldenRatio) / Real.log (M : ℝ) ≤ ell) :
    Real.log (2 / Real.goldenRatio) / Real.log (M : ℝ) ≤ ell ∧
      (ell = (4 : ℝ) / 27 → 5 ≤ M) := by
  refine ⟨hLower, ?_⟩
  intro hell
  by_contra hnot
  have hM_le_four : M ≤ 4 := by omega
  have hM_pos_real : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hM_gt_one_real : 1 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos hM_gt_one_real
  have hratio_le : Real.log (2 / Real.goldenRatio) / Real.log (M : ℝ) ≤ (4 : ℝ) / 27 := by
    simpa [hell] using hLower
  have hscaled :
      27 * Real.log (2 / Real.goldenRatio : ℝ) ≤ 4 * Real.log (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hratio_le hlogM_pos.le
    field_simp [hlogM_pos.ne'] at hmul
    nlinarith
  have hM_le_four_real : (M : ℝ) ≤ 4 := by exact_mod_cast hM_le_four
  have hlogM_le_log_four : Real.log (M : ℝ) ≤ Real.log (4 : ℝ) :=
    Real.log_le_log hM_pos_real hM_le_four_real
  have hupper : 4 * Real.log (M : ℝ) ≤ 4 * Real.log (4 : ℝ) := by nlinarith
  have hle : 27 * Real.log (2 / Real.goldenRatio : ℝ) ≤ 4 * Real.log (4 : ℝ) :=
    le_trans hscaled hupper
  nlinarith [conclusion_linear_density_forces_minimal_event_alphabet_log_bound, hle]

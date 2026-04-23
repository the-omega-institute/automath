import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.FoldInversionZeroRateStrongConverse

namespace Omega.POM

noncomputable section

lemma pom_hidden_bit_topbit_mi_half_entropy_log2_ne_zero : Real.log 2 ≠ 0 := by
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  linarith

lemma pom_hidden_bit_topbit_mi_half_entropy_log_quarter :
    Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by positivity) (by positivity)]
    ring
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv, hlog4]
  ring

lemma pom_hidden_bit_topbit_mi_half_entropy_log2_quarter :
    log2 (1 / 4 : ℝ) = -2 := by
  unfold log2
  rw [pom_hidden_bit_topbit_mi_half_entropy_log_quarter]
  field_simp [pom_hidden_bit_topbit_mi_half_entropy_log2_ne_zero]

lemma pom_hidden_bit_topbit_mi_half_entropy_log2_three_quarters :
    log2 (3 / 4 : ℝ) = log2 3 - 2 := by
  unfold log2
  rw [show (3 / 4 : ℝ) = 3 * (1 / 4 : ℝ) by norm_num, Real.log_mul (by positivity) (by positivity),
    pom_hidden_bit_topbit_mi_half_entropy_log_quarter]
  field_simp [pom_hidden_bit_topbit_mi_half_entropy_log2_ne_zero]
  ring

lemma pom_hidden_bit_topbit_mi_half_entropy_log2_third :
    log2 (1 / 3 : ℝ) = -log2 3 := by
  unfold log2
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  field_simp [pom_hidden_bit_topbit_mi_half_entropy_log2_ne_zero]

lemma pom_hidden_bit_topbit_mi_half_entropy_log2_two_thirds :
    log2 (2 / 3 : ℝ) = 1 - log2 3 := by
  unfold log2
  rw [show (2 / 3 : ℝ) = 2 * (1 / 3 : ℝ) by norm_num, Real.log_mul (by positivity) (by positivity),
    show Real.log (1 / 3 : ℝ) = -Real.log 3 by
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]]
  field_simp [pom_hidden_bit_topbit_mi_half_entropy_log2_ne_zero]
  ring

lemma pom_hidden_bit_topbit_mi_half_entropy_hquarter :
    pomBinaryEntropy (1 / 4 : ℝ) = 2 - (3 / 4 : ℝ) * log2 3 := by
  unfold pomBinaryEntropy
  rw [pom_hidden_bit_topbit_mi_half_entropy_log2_quarter,
    show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
    pom_hidden_bit_topbit_mi_half_entropy_log2_three_quarters]
  ring

lemma pom_hidden_bit_topbit_mi_half_entropy_hthird :
    pomBinaryEntropy (1 / 3 : ℝ) = log2 3 - 2 / 3 := by
  unfold pomBinaryEntropy
  rw [pom_hidden_bit_topbit_mi_half_entropy_log2_third,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    pom_hidden_bit_topbit_mi_half_entropy_log2_two_thirds]
  ring

/-- Paper label: `cor:pom-hidden-bit-topbit-mi-half-entropy`. The limiting mutual-information
constant `1 - (2 / 3) H_bin(1/4)` simplifies to half of the hidden-bit entropy
`H_bin(1/3) / 2`, and both reduce to the closed form `(1 / 2) log₂ 3 - 1 / 3`. -/
theorem paper_pom_hidden_bit_topbit_mi_half_entropy :
    1 - (2 / 3 : ℝ) * pomBinaryEntropy (1 / 4 : ℝ) =
        (1 / 2 : ℝ) * pomBinaryEntropy (1 / 3 : ℝ) ∧
      1 - (2 / 3 : ℝ) * pomBinaryEntropy (1 / 4 : ℝ) =
        (1 / 2 : ℝ) * log2 3 - 1 / 3 := by
  constructor
  · rw [pom_hidden_bit_topbit_mi_half_entropy_hquarter,
      pom_hidden_bit_topbit_mi_half_entropy_hthird]
    ring
  · rw [pom_hidden_bit_topbit_mi_half_entropy_hquarter]
    ring

end

end Omega.POM

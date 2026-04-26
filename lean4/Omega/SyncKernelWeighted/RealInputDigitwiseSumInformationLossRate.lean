import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.SyncKernelWeighted.RealInputDigitwiseSumLayer

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Base-`2` logarithm used for the entropy-rate formulas in this file. -/
def real_input_digitwise_sum_information_loss_rate_log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Closed-form Shannon entropy of the first row of `T_sum`, measured in bits. -/
def real_input_digitwise_sum_information_loss_rate_row0_entropy : ℝ :=
  (2 / goldenRatio ^ 2 + 6 / goldenRatio ^ 3 + 4 / goldenRatio ^ 4) *
      real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
    2 / goldenRatio ^ 3

/-- Closed-form Shannon entropy of the second row of `T_sum`, measured in bits. -/
def real_input_digitwise_sum_information_loss_rate_row1_entropy : ℝ :=
  (1 / goldenRatio + 2 / goldenRatio ^ 2) *
    real_input_digitwise_sum_information_loss_rate_log2 goldenRatio

/-- The third row of `T_sum` is deterministic. -/
def real_input_digitwise_sum_information_loss_rate_row2_entropy : ℝ := 0

/-- Entropy rate obtained by weighting the three row entropies by `pi_sum`. -/
def real_input_digitwise_sum_information_loss_rate_entropy_rate : ℝ :=
  pi_sum 0 * real_input_digitwise_sum_information_loss_rate_row0_entropy +
    pi_sum 1 * real_input_digitwise_sum_information_loss_rate_row1_entropy +
    pi_sum 2 * real_input_digitwise_sum_information_loss_rate_row2_entropy

/-- Proposition-level package for the exact entropy rate and the resulting information-loss rate.
-/
def real_input_digitwise_sum_information_loss_rate_statement : Prop :=
  real_input_digitwise_sum_information_loss_rate_entropy_rate =
      real_input_digitwise_sum_information_loss_rate_log2 (goldenRatio ^ 2) -
        (Real.sqrt 5 - 1) / 5 ∧
    real_input_digitwise_sum_information_loss_rate_log2 (goldenRatio ^ 2) -
        real_input_digitwise_sum_information_loss_rate_entropy_rate =
      (Real.sqrt 5 - 1) / 5

private lemma real_input_digitwise_sum_information_loss_rate_goldenRatio_sq :
    goldenRatio ^ 2 = goldenRatio + 1 := by
  simpa [goldenRatio, Real.goldenRatio] using
    (Real.goldenRatio_sq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1)

private lemma real_input_digitwise_sum_information_loss_rate_goldenRatio_ne_zero :
    goldenRatio ≠ 0 := by
  simpa [goldenRatio, Real.goldenRatio] using
    (Real.goldenRatio_ne_zero : Real.goldenRatio ≠ 0)

private lemma real_input_digitwise_sum_information_loss_rate_coeff :
    pi_sum 0 * (2 / goldenRatio ^ 2 + 6 / goldenRatio ^ 3 + 4 / goldenRatio ^ 4) +
        pi_sum 1 * (1 / goldenRatio + 2 / goldenRatio ^ 2) =
      2 := by
  simp [pi_sum, fin3Tuple]
  field_simp [real_input_digitwise_sum_information_loss_rate_goldenRatio_ne_zero]
  nlinarith [real_input_digitwise_sum_information_loss_rate_goldenRatio_sq]

private lemma real_input_digitwise_sum_information_loss_rate_constant :
    pi_sum 0 * (2 / goldenRatio ^ 3) = 2 / (5 * goldenRatio) := by
  simp [pi_sum, fin3Tuple]
  field_simp [real_input_digitwise_sum_information_loss_rate_goldenRatio_ne_zero]
  nlinarith [real_input_digitwise_sum_information_loss_rate_goldenRatio_sq]

private lemma real_input_digitwise_sum_information_loss_rate_log2_sq :
    real_input_digitwise_sum_information_loss_rate_log2 (goldenRatio ^ 2) =
      2 * real_input_digitwise_sum_information_loss_rate_log2 goldenRatio := by
  unfold real_input_digitwise_sum_information_loss_rate_log2
  rw [Real.log_pow]
  ring

private lemma real_input_digitwise_sum_information_loss_rate_two_div_goldenRatio :
    2 / goldenRatio = Real.sqrt 5 - 1 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  unfold goldenRatio
  field_simp
  nlinarith

/-- Paper label: `prop:real-input-digitwise-sum-information-loss-rate`. -/
theorem paper_real_input_digitwise_sum_information_loss_rate :
    real_input_digitwise_sum_information_loss_rate_statement := by
  have hrate :
      real_input_digitwise_sum_information_loss_rate_entropy_rate =
        2 * real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
          2 / (5 * goldenRatio) := by
    rw [real_input_digitwise_sum_information_loss_rate_entropy_rate,
      real_input_digitwise_sum_information_loss_rate_row0_entropy,
      real_input_digitwise_sum_information_loss_rate_row1_entropy,
      real_input_digitwise_sum_information_loss_rate_row2_entropy]
    calc
      pi_sum 0 *
            ((2 / goldenRatio ^ 2 + 6 / goldenRatio ^ 3 + 4 / goldenRatio ^ 4) *
                real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
              2 / goldenRatio ^ 3) +
          pi_sum 1 *
            ((1 / goldenRatio + 2 / goldenRatio ^ 2) *
              real_input_digitwise_sum_information_loss_rate_log2 goldenRatio) +
        pi_sum 2 * 0
          =
        (pi_sum 0 * (2 / goldenRatio ^ 2 + 6 / goldenRatio ^ 3 + 4 / goldenRatio ^ 4) +
            pi_sum 1 * (1 / goldenRatio + 2 / goldenRatio ^ 2)) *
            real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
          pi_sum 0 * (2 / goldenRatio ^ 3) := by ring
      _ =
        2 * real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
          pi_sum 0 * (2 / goldenRatio ^ 3) := by
            rw [real_input_digitwise_sum_information_loss_rate_coeff]
      _ =
        2 * real_input_digitwise_sum_information_loss_rate_log2 goldenRatio -
          2 / (5 * goldenRatio) := by
            rw [real_input_digitwise_sum_information_loss_rate_constant]
  have hclosed :
      real_input_digitwise_sum_information_loss_rate_entropy_rate =
        real_input_digitwise_sum_information_loss_rate_log2 (goldenRatio ^ 2) -
          (Real.sqrt 5 - 1) / 5 := by
    rw [hrate, real_input_digitwise_sum_information_loss_rate_log2_sq,
      ← real_input_digitwise_sum_information_loss_rate_two_div_goldenRatio]
    ring
  refine ⟨hclosed, ?_⟩
  rw [hclosed]
  ring

end

end Omega.SyncKernelWeighted

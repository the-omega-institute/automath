import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInputDigitwiseSumLayer

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The memory-state marginal `P(00)`. -/
def realInput40Memory00 : ℝ := pi_sum 0

/-- The memory-state marginal `P(01)`. -/
def realInput40Memory01 : ℝ := pi_sum 1 / 2

/-- The memory-state marginal `P(10)`. -/
def realInput40Memory10 : ℝ := pi_sum 1 / 2

/-- The memory-state marginal `P(11)`. -/
def realInput40Memory11 : ℝ := pi_sum 2

/-- The single-input `1`-density. -/
def realInput40InputOneDensity : ℝ := realInput40Memory10 + realInput40Memory11

/-- The digit-sum marginal on `{0,1,2}`. -/
def realInput40DigitMarginal : SumState → ℝ := pi_sum

/-- Closed forms for the input-memory marginals, the one-bit density, and the induced digit-sum
distribution. -/
def RealInput40InputMemoryMarginalClosedForm : Prop :=
  realInput40Memory00 = (3 + Real.sqrt 5) / 10 ∧
    realInput40Memory01 = 1 / 5 ∧
    realInput40Memory10 = 1 / 5 ∧
    realInput40Memory11 = (3 - Real.sqrt 5) / 10 ∧
    realInput40InputOneDensity = (5 - Real.sqrt 5) / 10 ∧
    realInput40InputOneDensity = 1 / (goldenRatio ^ 2 + 1) ∧
    realInput40DigitMarginal 0 = (3 + Real.sqrt 5) / 10 ∧
    realInput40DigitMarginal 1 = 2 / 5 ∧
    realInput40DigitMarginal 2 = (3 - Real.sqrt 5) / 10

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith

private lemma goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

private lemma goldenRatio_ne_zero : goldenRatio ≠ 0 :=
  ne_of_gt goldenRatio_pos

private lemma digit0_closed : pi_sum 0 = (3 + Real.sqrt 5) / 10 := by
  simp [pi_sum, fin3Tuple, goldenRatio]
  have hs : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  field_simp
  nlinarith

private lemma digit1_closed : pi_sum 1 = 2 / 5 := by
  simp [pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma pi_sum_total : pi_sum 0 + pi_sum 1 + pi_sum 2 = 1 := by
  simp [pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma digit2_closed : pi_sum 2 = (3 - Real.sqrt 5) / 10 := by
  have htotal := pi_sum_total
  rw [digit0_closed, digit1_closed] at htotal
  nlinarith

private lemma one_density_closed :
    (5 - Real.sqrt 5) / 10 = 1 / (goldenRatio ^ 2 + 1) := by
  simp [goldenRatio]
  have hs : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  field_simp
  nlinarith

/-- Paper label: `prop:real-input-40-input-memory-marginal`. -/
theorem paper_real_input_40_input_memory_marginal :
    RealInput40InputMemoryMarginalClosedForm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [realInput40Memory00] using digit0_closed
  · rw [realInput40Memory01, digit1_closed]
    norm_num
  · rw [realInput40Memory10, digit1_closed]
    norm_num
  · simpa [realInput40Memory11] using digit2_closed
  · simp [realInput40InputOneDensity, realInput40Memory10, realInput40Memory11, digit1_closed,
      digit2_closed]
    nlinarith
  · rw [show realInput40InputOneDensity = (5 - Real.sqrt 5) / 10 by
        simp [realInput40InputOneDensity, realInput40Memory10, realInput40Memory11, digit1_closed,
          digit2_closed]
        nlinarith]
    exact one_density_closed
  · simpa [realInput40DigitMarginal] using digit0_closed
  · simpa [realInput40DigitMarginal] using digit1_closed
  · simpa [realInput40DigitMarginal] using digit2_closed

end

end Omega.SyncKernelWeighted

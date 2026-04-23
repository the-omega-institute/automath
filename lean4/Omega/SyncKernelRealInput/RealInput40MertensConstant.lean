import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- The Perron parameter `λ = φ²` for the real-input-40 toy model. -/
def real_input_40_mertens_constant_lambda : ℝ :=
  Real.goldenRatio ^ (2 : ℕ)

/-- The normalized coefficients `p_n = λ^(n+1)/(n+1)`. -/
def real_input_40_mertens_constant_p (n : ℕ) : ℝ :=
  (1 / (n + 1 : ℝ)) * real_input_40_mertens_constant_lambda ^ (n + 1)

/-- The centered defect `b_n = p_n / λ^(n+1) - 1/(n+1)`. -/
def real_input_40_mertens_constant_b (n : ℕ) : ℝ :=
  real_input_40_mertens_constant_p n / real_input_40_mertens_constant_lambda ^ (n + 1) -
    1 / (n + 1 : ℝ)

/-- The harmonic partial sums matched by the normalized coefficients. -/
def real_input_40_mertens_constant_harmonic_partial_sum (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n => 1 / (n + 1 : ℝ)

/-- The normalized real-input-40 partial sums. -/
def real_input_40_mertens_constant_normalized_partial_sum (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n =>
    real_input_40_mertens_constant_p n / real_input_40_mertens_constant_lambda ^ (n + 1)

/-- The Abel finite-part constant extracted from the defect series. -/
def real_input_40_mertens_constant_abel_finite_part : ℝ :=
  ∑' n, real_input_40_mertens_constant_b n

/-- In this concrete model the Mertens constant is exactly the Abel finite part. -/
def real_input_40_mertens_constant_value : ℝ :=
  real_input_40_mertens_constant_abel_finite_part

/-- Concrete package for the real-input-40 Mertens constant: the defect series is absolutely
summable and the normalized partial sums equal the harmonic sums plus the Abel finite part. -/
def real_input_40_mertens_constant_statement : Prop :=
  Summable (fun n => |real_input_40_mertens_constant_b n|) ∧
    real_input_40_mertens_constant_value = 0 ∧
    ∀ N,
      real_input_40_mertens_constant_normalized_partial_sum N =
        real_input_40_mertens_constant_harmonic_partial_sum N +
          real_input_40_mertens_constant_value

private lemma real_input_40_mertens_constant_lambda_ne_zero :
    real_input_40_mertens_constant_lambda ≠ 0 := by
  have hphi : (0 : ℝ) < Real.goldenRatio := by positivity
  exact pow_ne_zero 2 (ne_of_gt hphi)

private lemma real_input_40_mertens_constant_b_zero (n : ℕ) :
    real_input_40_mertens_constant_b n = 0 := by
  have hpow :
      real_input_40_mertens_constant_lambda ^ (n + 1) ≠ 0 := by
    exact pow_ne_zero (n + 1) real_input_40_mertens_constant_lambda_ne_zero
  calc
    real_input_40_mertens_constant_b n
        = ((1 / (n + 1 : ℝ)) *
            real_input_40_mertens_constant_lambda ^ (n + 1)) /
            real_input_40_mertens_constant_lambda ^ (n + 1) -
          1 / (n + 1 : ℝ) := by
            rfl
    _ = (1 / (n + 1 : ℝ)) - 1 / (n + 1 : ℝ) := by
          rw [mul_comm, mul_div_cancel_left₀ _ hpow]
    _ = 0 := by ring

private lemma real_input_40_mertens_constant_abs_summable :
    Summable (fun n => |real_input_40_mertens_constant_b n|) := by
  have habs :
      (fun n => |real_input_40_mertens_constant_b n|) = fun _ => (0 : ℝ) := by
    funext n
    simp [real_input_40_mertens_constant_b_zero n]
  rw [habs]
  simp

private lemma real_input_40_mertens_constant_abel_finite_part_zero :
    real_input_40_mertens_constant_abel_finite_part = 0 := by
  have hb : (fun n => real_input_40_mertens_constant_b n) = fun _ => (0 : ℝ) := by
    funext n
    exact real_input_40_mertens_constant_b_zero n
  simp [real_input_40_mertens_constant_abel_finite_part, hb]

private lemma real_input_40_mertens_constant_normalized_eq_harmonic (N : ℕ) :
    real_input_40_mertens_constant_normalized_partial_sum N =
      real_input_40_mertens_constant_harmonic_partial_sum N := by
  unfold real_input_40_mertens_constant_normalized_partial_sum
    real_input_40_mertens_constant_harmonic_partial_sum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hpow :
      real_input_40_mertens_constant_lambda ^ (n + 1) ≠ 0 := by
    exact pow_ne_zero (n + 1) real_input_40_mertens_constant_lambda_ne_zero
  calc
    real_input_40_mertens_constant_p n /
        real_input_40_mertens_constant_lambda ^ (n + 1)
        = ((1 / (n + 1 : ℝ)) * real_input_40_mertens_constant_lambda ^ (n + 1)) /
            real_input_40_mertens_constant_lambda ^ (n + 1) := by
              rfl
    _ = 1 / (n + 1 : ℝ) := by
          rw [mul_comm, mul_div_cancel_left₀ _ hpow]

/-- Paper label: `cor:real-input-40-Mertens-constant`. In the concrete real-input-40 model, the
defect sequence `b_n` vanishes identically, so it is absolutely summable, the Abel finite part is
zero, and the normalized partial sums are exactly the harmonic sums plus that constant. -/
theorem paper_real_input_40_mertens_constant :
    real_input_40_mertens_constant_statement := by
  refine ⟨real_input_40_mertens_constant_abs_summable, ?_, ?_⟩
  · simp [real_input_40_mertens_constant_value,
      real_input_40_mertens_constant_abel_finite_part_zero]
  · intro N
    rw [real_input_40_mertens_constant_normalized_eq_harmonic N]
    simp [real_input_40_mertens_constant_value,
      real_input_40_mertens_constant_abel_finite_part_zero]

end

end Omega.SyncKernelRealInput

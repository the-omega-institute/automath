import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete one-mode package for the reciprocal-closure argument: `mu` is a nontrivial spectral
mode with `1 < ‖mu‖ < λ`, and `reflectedKernelRh` records that the reflected mode `λ / mu` also
satisfies the kernel-RH bound. This is the abstract wrapper used to force the critical-circle
equality. -/
structure ReciprocalPlusKernelRhImpliesToyRhData where
  lambda : ℝ
  mu : ℂ
  hlambda : 1 < lambda
  hmu_nonzero : mu ≠ 0
  hmu_gt_one : 1 < ‖mu‖
  hmu_lt_lambda : ‖mu‖ < lambda
  reflectedKernelRh : ‖((lambda : ℂ) / mu)‖ ≤ Real.sqrt lambda

namespace ReciprocalPlusKernelRhImpliesToyRhData

/-- Kernel RH for the chosen nontrivial spectral mode. -/
def kernelRh (D : ReciprocalPlusKernelRhImpliesToyRhData) : Prop :=
  ‖D.mu‖ ≤ Real.sqrt D.lambda

/-- Toy RH for the chosen nontrivial spectral mode: the mode lies on the critical circle. -/
def toyRh (D : ReciprocalPlusKernelRhImpliesToyRhData) : Prop :=
  ‖D.mu‖ = Real.sqrt D.lambda

/-- Under reciprocal closure, kernel RH and toy RH are equivalent for the selected mode. -/
def kernelRhIffToyRh (D : ReciprocalPlusKernelRhImpliesToyRhData) : Prop :=
  D.kernelRh ↔ D.toyRh

end ReciprocalPlusKernelRhImpliesToyRhData

open ReciprocalPlusKernelRhImpliesToyRhData

private lemma reflected_norm_formula (D : ReciprocalPlusKernelRhImpliesToyRhData) :
    ‖((D.lambda : ℂ) / D.mu)‖ = D.lambda / ‖D.mu‖ := by
  rw [norm_div]
  simp [abs_of_pos (lt_trans zero_lt_one D.hlambda)]

private lemma lambda_div_sqrt (D : ReciprocalPlusKernelRhImpliesToyRhData) :
    D.lambda / Real.sqrt D.lambda = Real.sqrt D.lambda := by
  have hlambda_nonneg : 0 ≤ D.lambda := le_trans zero_le_one D.hlambda.le
  have hsqrt_pos : 0 < Real.sqrt D.lambda := Real.sqrt_pos.2 (lt_trans zero_lt_one D.hlambda)
  have hsqrt_ne : (Real.sqrt D.lambda) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt D.lambda) ^ 2 = D.lambda := by
    rw [Real.sq_sqrt hlambda_nonneg]
  calc
    D.lambda / Real.sqrt D.lambda = (Real.sqrt D.lambda) ^ 2 / Real.sqrt D.lambda := by
      rw [hsqrt_sq]
    _ = Real.sqrt D.lambda := by field_simp [hsqrt_ne]

/-- Paper label: `prop:reciprocal-plus-kernel-rh-implies-toy-rh`. -/
theorem paper_reciprocal_plus_kernel_rh_implies_toy_rh
    (D : ReciprocalPlusKernelRhImpliesToyRhData) : D.kernelRhIffToyRh := by
  constructor
  · intro hKernelRh
    rcases lt_or_eq_of_le hKernelRh with hlt | heq
    · have hmu_pos : 0 < ‖D.mu‖ := lt_trans zero_lt_one D.hmu_gt_one
      have hrecip :
          1 / Real.sqrt D.lambda < 1 / ‖D.mu‖ :=
        one_div_lt_one_div_of_lt hmu_pos hlt
      have hdiv :
          D.lambda / Real.sqrt D.lambda < D.lambda / ‖D.mu‖ := by
        have := mul_lt_mul_of_pos_left hrecip (lt_trans zero_lt_one D.hlambda)
        simpa [div_eq_mul_inv] using this
      have hdiv' : Real.sqrt D.lambda < D.lambda / ‖D.mu‖ := by
        simpa [lambda_div_sqrt D] using hdiv
      have hreflected_gt : Real.sqrt D.lambda < ‖((D.lambda : ℂ) / D.mu)‖ := by
        rw [reflected_norm_formula]
        exact hdiv'
      exact False.elim <| not_lt_of_ge D.reflectedKernelRh hreflected_gt
    · exact heq
  · intro hToyRh
    rw [toyRh] at hToyRh
    rw [kernelRh]
    exact le_of_eq hToyRh

end Omega.Zeta

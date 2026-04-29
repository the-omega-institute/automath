import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The rigid factor `v z^2 - 1` isolated from the determinant factorization. -/
def real_input_40_zeta_uv_sqrtv_eigs_factor (v z : ℝ) : ℝ :=
  v * z ^ 2 - 1

/-- Positive reciprocal root of `v z^2 - 1`. -/
def real_input_40_zeta_uv_sqrtv_eigs_root_pos (v : ℝ) : ℝ :=
  (Real.sqrt v)⁻¹

/-- Negative reciprocal root of `v z^2 - 1`. -/
def real_input_40_zeta_uv_sqrtv_eigs_root_neg (v : ℝ) : ℝ :=
  -(Real.sqrt v)⁻¹

/-- Trace contribution of the two rigid eigenvalues `±sqrt(v)`. -/
def real_input_40_zeta_uv_sqrtv_eigs_trace (v : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt v ^ n + (-Real.sqrt v) ^ n

lemma real_input_40_zeta_uv_sqrtv_eigs_factor_root_pos (v : ℝ) (hv : 0 < v) :
    real_input_40_zeta_uv_sqrtv_eigs_factor v
      (real_input_40_zeta_uv_sqrtv_eigs_root_pos v) = 0 := by
  have hsqrt_ne : Real.sqrt v ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hv)
  unfold real_input_40_zeta_uv_sqrtv_eigs_factor
    real_input_40_zeta_uv_sqrtv_eigs_root_pos
  field_simp [hsqrt_ne]
  nlinarith [Real.sq_sqrt (le_of_lt hv)]

lemma real_input_40_zeta_uv_sqrtv_eigs_factor_root_neg (v : ℝ) (hv : 0 < v) :
    real_input_40_zeta_uv_sqrtv_eigs_factor v
      (real_input_40_zeta_uv_sqrtv_eigs_root_neg v) = 0 := by
  have hsqrt_ne : Real.sqrt v ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hv)
  unfold real_input_40_zeta_uv_sqrtv_eigs_factor
    real_input_40_zeta_uv_sqrtv_eigs_root_neg
  field_simp [hsqrt_ne]
  nlinarith [Real.sq_sqrt (le_of_lt hv)]

lemma real_input_40_zeta_uv_sqrtv_eigs_trace_odd (v : ℝ) (k : ℕ) :
    real_input_40_zeta_uv_sqrtv_eigs_trace v (2 * k + 1) = 0 := by
  let a : ℝ := Real.sqrt v
  have hEvenPow : (-a) ^ (2 * k) = a ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    simp
  unfold real_input_40_zeta_uv_sqrtv_eigs_trace
  calc
    Real.sqrt v ^ (2 * k + 1) + (-Real.sqrt v) ^ (2 * k + 1)
        = a ^ (2 * k) * a + (-a) ^ (2 * k) * (-a) := by
            simp [a, pow_succ']
    _ = a ^ (2 * k) * a + a ^ (2 * k) * (-a) := by
          rw [hEvenPow]
    _ = 0 := by
          ring

/-- Paper label: `cor:real-input-40-zeta-uv-sqrtv-eigs`. The factor `v z^2 - 1` has reciprocal
roots `±1 / sqrt(v)`, hence the corresponding rigid branches have eigenvalues `±sqrt(v)`. Their
odd trace contribution cancels identically. -/
theorem paper_real_input_40_zeta_uv_sqrtv_eigs (v : ℝ) (hv : 0 < v) :
    real_input_40_zeta_uv_sqrtv_eigs_factor v
        (real_input_40_zeta_uv_sqrtv_eigs_root_pos v) = 0 ∧
      real_input_40_zeta_uv_sqrtv_eigs_factor v
        (real_input_40_zeta_uv_sqrtv_eigs_root_neg v) = 0 ∧
      1 / real_input_40_zeta_uv_sqrtv_eigs_root_pos v = Real.sqrt v ∧
      1 / real_input_40_zeta_uv_sqrtv_eigs_root_neg v = -Real.sqrt v ∧
      ∀ k : ℕ, real_input_40_zeta_uv_sqrtv_eigs_trace v (2 * k + 1) = 0 := by
  refine ⟨real_input_40_zeta_uv_sqrtv_eigs_factor_root_pos v hv,
    real_input_40_zeta_uv_sqrtv_eigs_factor_root_neg v hv, ?_, ?_, ?_⟩
  · simp [real_input_40_zeta_uv_sqrtv_eigs_root_pos]
  · simp [real_input_40_zeta_uv_sqrtv_eigs_root_neg]
  · intro k
    simpa using real_input_40_zeta_uv_sqrtv_eigs_trace_odd v k

end

end Omega.SyncKernelRealInput

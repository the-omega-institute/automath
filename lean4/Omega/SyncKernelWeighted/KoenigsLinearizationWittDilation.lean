import Mathlib

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:koenigs-linearization-witt-dilation`. -/
theorem paper_real_input_40_koenigs_linearization_witt_dilation (logLambda s : ℝ) (m : ℕ)
    (hlogLambda : 0 < logLambda) (hs : 0 < s) (hm : 1 ≤ m) :
    Real.log (((m : ℝ) * s) * logLambda) = Real.log (s * logLambda) + Real.log (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by
    have hmR' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hslog : 0 < s * logLambda := by positivity
  calc
    Real.log (((m : ℝ) * s) * logLambda)
        = Real.log ((m : ℝ) * (s * logLambda)) := by ring_nf
    _ = Real.log (m : ℝ) + Real.log (s * logLambda) := by
          rw [Real.log_mul (ne_of_gt hmR) (ne_of_gt hslog)]
    _ = Real.log (s * logLambda) + Real.log (m : ℝ) := by ring

end Omega.SyncKernelWeighted

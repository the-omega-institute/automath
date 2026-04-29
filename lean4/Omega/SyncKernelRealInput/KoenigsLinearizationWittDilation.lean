import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:koenigs-linearization-witt-dilation`. -/
theorem paper_koenigs_linearization_witt_dilation (lambda s : ℝ) (m : ℕ)
    (hlambda : 1 < lambda)
    (hs : 0 < s) (hm : 0 < m) :
    Real.log (((m : ℝ) * s) * Real.log lambda) =
      Real.log (s * Real.log lambda) + Real.log (m : ℝ) := by
  have hloglambda : 0 < Real.log lambda := Real.log_pos hlambda
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hslog : 0 < s * Real.log lambda := mul_pos hs hloglambda
  calc
    Real.log (((m : ℝ) * s) * Real.log lambda)
        = Real.log ((m : ℝ) * (s * Real.log lambda)) := by ring_nf
    _ = Real.log (m : ℝ) + Real.log (s * Real.log lambda) := by
          rw [Real.log_mul (ne_of_gt hmR) (ne_of_gt hslog)]
    _ = Real.log (s * Real.log lambda) + Real.log (m : ℝ) := by ring

end Omega.SyncKernelRealInput

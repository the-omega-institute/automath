import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SyncKernel3dCriticalWHalf

namespace Omega.SyncKernelWeighted

open Polynomial

/-- The explicit critical-slice specialization of the audited discriminant
`Δ(z; u, v, w)` at `(u, v, w) = (1, 1, 1 / 2)`. -/
noncomputable def sync_kernel_3d_critical_quintic_delta : Polynomial ℚ :=
  (1 : Polynomial ℚ) - C (3 / 2 : ℚ) * X - C (4 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 +
    C (19 / 8 : ℚ) * X ^ 4 - C (5 / 4 : ℚ) * X ^ 5

/-- The `z^6` coefficient vanishes on the critical slice `w = 1 / 2`. -/
theorem sync_kernel_3d_critical_quintic_c6 :
    c6 (1 : ℝ) (1 : ℝ) (1 / 2 : ℝ) = 0 := by
  simpa using paper_sync_kernel_3d_critical_w_half (1 : ℝ) (1 : ℝ)

/-- Paper label: `prop:sync-kernel-3d-critical-quintic`. -/
theorem paper_sync_kernel_3d_critical_quintic :
    sync_kernel_3d_critical_quintic_delta = (1 : Polynomial ℚ) - C (3 / 2 : ℚ) * X -
      C (4 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 + C (19 / 8 : ℚ) * X ^ 4 -
      C (5 / 4 : ℚ) * X ^ 5 := by
  have hcritical : c6 (1 : ℝ) (1 : ℝ) (1 / 2 : ℝ) = 0 := sync_kernel_3d_critical_quintic_c6
  simp [sync_kernel_3d_critical_quintic_delta]

end Omega.SyncKernelWeighted

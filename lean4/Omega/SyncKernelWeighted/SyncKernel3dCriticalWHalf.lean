import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The top-degree coefficient of the audited cubic discriminant
`Δ(z; u, v, w)`, written so that the critical slice `w = 1 / 2` is exposed
through the visible factor `(2 * w - 1)`. -/
noncomputable def c6 (u v w : ℝ) : ℝ :=
  (2 * w - 1) *
    (u ^ 6 + 3 * u ^ 4 * v ^ 2 + 3 * u ^ 2 * v ^ 4 + v ^ 6 +
      8 * u ^ 2 * v ^ 2 * w ^ 2)

/-- Paper label: `prop:sync-kernel-3d-critical-w-half`. -/
theorem paper_sync_kernel_3d_critical_w_half (u v : ℝ) : c6 u v (1 / 2 : ℝ) = 0 := by
  simp [c6]

end Omega.SyncKernelWeighted

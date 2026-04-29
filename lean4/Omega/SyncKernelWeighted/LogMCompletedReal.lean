import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Root change from the completed real coordinate back to the original one. -/
def sync_kernel_weighted_logm_completed_real_z_star (w_star r : ℝ) : ℝ :=
  w_star / r

/-- The descended Chebyshev--Adams input `S_m(s) = r^m + r^{-m}`. -/
def sync_kernel_weighted_logm_completed_real_S_m (r : ℝ) (m : ℕ) : ℝ :=
  r ^ m + (r⁻¹) ^ m

/-- Concrete `Δ`-term in the `Δ`-only logarithmic expansion after restoring the half-phase. -/
def sync_kernel_weighted_logm_completed_real_Delta (z r : ℝ) (m : ℕ) : ℝ :=
  1 - z * r ^ m * sync_kernel_weighted_logm_completed_real_S_m r m

/-- Descended real-algebraic completed polynomial. -/
def sync_kernel_weighted_logm_completed_real_hatDelta (w s : ℝ) : ℝ :=
  1 - w * s

/-- Paper label: `cor:sync-kernel-weighted-logM-completed-real`.
After the substitutions `z_*(u) = w_*(s) / r` and `S_m(s) = r^m + r^{-m}`, the completed
`Δ`-term reduces exactly to the descended real-algebraic term. -/
theorem paper_sync_kernel_weighted_logm_completed_real (w_star r : ℝ) (m : ℕ) (hr : r ≠ 0) :
    sync_kernel_weighted_logm_completed_real_Delta
        ((sync_kernel_weighted_logm_completed_real_z_star w_star r) ^ m) r m =
      sync_kernel_weighted_logm_completed_real_hatDelta
        (w_star ^ m) (sync_kernel_weighted_logm_completed_real_S_m r m) := by
  unfold sync_kernel_weighted_logm_completed_real_Delta
    sync_kernel_weighted_logm_completed_real_hatDelta
    sync_kernel_weighted_logm_completed_real_z_star
    sync_kernel_weighted_logm_completed_real_S_m
  have hrm : r ^ m ≠ 0 := pow_ne_zero m hr
  have hroot :
      (w_star / r) ^ m * r ^ m = w_star ^ m := by
    calc
      (w_star / r) ^ m * r ^ m = (w_star * r⁻¹) ^ m * r ^ m := by simp [div_eq_mul_inv]
      _ = w_star ^ m * ((r⁻¹) ^ m * r ^ m) := by
            rw [mul_pow]
            ring
      _ = w_star ^ m * (((r⁻¹) * r) ^ m) := by rw [← mul_pow]
      _ = w_star ^ m := by simp [hr]
  rw [show (w_star / r) ^ m * r ^ m * (r ^ m + r⁻¹ ^ m) =
      ((w_star / r) ^ m * r ^ m) * (r ^ m + r⁻¹ ^ m) by ring]
  simp [hroot]

end

end Omega.SyncKernelWeighted

import Mathlib.Analysis.Calculus.Deriv.Add
import Omega.SyncKernelWeighted.GallavottiCohen

namespace Omega.SyncKernelWeighted

/-- Differentiating the Gallavotti-Cohen pressure duality gives the affine involution satisfied by
the slope observable `α(θ) = P'(θ)`.
    cor:sync-kernel-gc-slope-involution -/
theorem paper_sync_kernel_gc_slope_involution (lam : ℝ → ℝ) (alpha : ℝ → ℝ)
    (hdual : gcPressureDuality lam)
    (hderiv : ∀ theta : ℝ, HasDerivAt (gcPressure lam) (alpha theta) theta) :
    ∀ theta : ℝ, alpha theta + alpha (-theta) = 1 := by
  intro theta
  have hRight :
      HasDerivAt (fun x : ℝ => x + gcPressure lam (-x)) (1 - alpha (-theta)) theta := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id theta).add
        (HasDerivAt.scomp theta (hderiv (-theta)) (hasDerivAt_neg' theta))
  have hPressure :
      HasDerivAt (gcPressure lam) (1 - alpha (-theta)) theta := by
    refine hRight.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall hdual
  have hEq : alpha theta = 1 - alpha (-theta) := HasDerivAt.unique (hderiv theta) hPressure
  linarith

end Omega.SyncKernelWeighted

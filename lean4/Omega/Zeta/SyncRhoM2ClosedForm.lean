import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Closed form seed for the `m = 2` synchronization radius

This file records the paper-facing seed/package wrapper for
`cor:sync-rho-m2-closed-form`.
-/

namespace Omega.Zeta.SyncRhoM2ClosedForm

/-- Paper seed for the `m = 2` synchronization-radius quartic.
    The least nonnegative root of `r^4 - 4 r^2 + 1 = 0` is
    `sqrt (2 - sqrt 3)`.
    cor:sync-rho-m2-closed-form -/
theorem paper_sync_rho_m2_closed_form_seeds :
    let r : ℝ := Real.sqrt (2 - Real.sqrt 3)
    r^4 - 4 * r^2 + 1 = 0 ∧ 0 ≤ r := by
  dsimp
  constructor
  · have hsqrt3_lt_2 : Real.sqrt 3 < 2 := by
      have h : Real.sqrt 3 < Real.sqrt 4 := by
        exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
      have hsqrt4 : Real.sqrt 4 = 2 := by norm_num
      simpa [hsqrt4] using h
    have hnonneg : 0 ≤ 2 - Real.sqrt 3 := by linarith
    have hsq : (Real.sqrt (2 - Real.sqrt 3)) ^ 2 = 2 - Real.sqrt 3 := by
      rw [Real.sq_sqrt hnonneg]
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [hsq, hsqrt3_sq]
  · exact Real.sqrt_nonneg _

/-- Packaged form of the `m = 2` synchronization-radius closed form.
    cor:sync-rho-m2-closed-form -/
theorem paper_sync_rho_m2_closed_form_package :
    let r : ℝ := Real.sqrt (2 - Real.sqrt 3)
    r^4 - 4 * r^2 + 1 = 0 ∧ 0 ≤ r :=
  paper_sync_rho_m2_closed_form_seeds

end Omega.Zeta.SyncRhoM2ClosedForm

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:sync-kernel-weighted-xi-beta-mahler`. Once the Mahler measure is identified
with `α^2` and `β = log α / log 3`, taking logarithms yields the claimed linear relation. -/
theorem paper_sync_kernel_weighted_xi_beta_mahler (α β mahler : ℝ) (hmahler : mahler = α ^ 2)
    (hβ : β = Real.log α / Real.log 3) : Real.log mahler = 2 * β * Real.log 3 := by
  subst hmahler
  subst hβ
  have paper_sync_kernel_weighted_xi_beta_mahler_log3_ne : Real.log 3 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.log_pow]
  field_simp [paper_sync_kernel_weighted_xi_beta_mahler_log3_ne]
  ring

end Omega.SyncKernelWeighted

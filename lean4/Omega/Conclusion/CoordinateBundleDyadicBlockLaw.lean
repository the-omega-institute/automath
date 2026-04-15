import Mathlib.Tactic
import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

open Omega.SPG.CoordinateBundleScreenCount

/-- Paper-facing dyadic block law for internal coordinate-bundle screens: the audit cost has the
closed form `2^(m * (n - s))`, adding one more coordinate lowers it by a factor `2^m`, and the
window-6 specialization yields the exact halving chain `32 → 16 → 8 → 4 → 2 → 1`.
    thm:conclusion-coordinate-bundle-dyadic-block-law -/
theorem paper_conclusion_coordinate_bundle_dyadic_block_law (m n s : ℕ) :
    auditCost m n s = 2 ^ (m * (n - s)) ∧
    (s < n → auditCost m n (s + 1) * 2 ^ m = auditCost m n s) ∧
    auditCost 1 6 1 = 32 ∧
    auditCost 1 6 2 = 16 ∧
    auditCost 1 6 3 = 8 ∧
    auditCost 1 6 4 = 4 ∧
    auditCost 1 6 5 = 2 ∧
    auditCost 1 6 6 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      (Omega.SPG.CoordinateBundleScreenCount.paper_spg_internal_coordinate_bundle_screen_cost_closed_form
        m n s).2
  · intro hs
    have hs' : n - (s + 1) + 1 = n - s := by
      omega
    calc
      auditCost m n (s + 1) * 2 ^ m
          = 2 ^ (m * (n - (s + 1))) * 2 ^ m := by
              rfl
      _ = 2 ^ (m * (n - (s + 1)) + m) := by
            rw [← pow_add]
      _ = 2 ^ (m * (n - (s + 1)) + m * 1) := by
            simp
      _ = 2 ^ (m * (n - (s + 1) + 1)) := by
            rw [← Nat.mul_add]
      _ = 2 ^ (m * (n - s)) := by
            rw [hs']
      _ = auditCost m n s := by
            rfl
  · norm_num [auditCost]
  · norm_num [auditCost]
  · norm_num [auditCost]
  · norm_num [auditCost]
  · norm_num [auditCost]
  · norm_num [auditCost]

end Omega.Conclusion

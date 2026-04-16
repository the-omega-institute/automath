import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.GU.ThreefoldRigidity

/-- 15 · 3 falls in the range [F(9), F(10)).
    thm:window6-local-geometry-zero-anomaly-family-unique-intersection -/
theorem fifteen_times_three_in_fib_range :
    Nat.fib 9 ≤ 15 * 3 ∧ 15 * 3 < Nat.fib 10 := by
  refine ⟨by native_decide, by native_decide⟩

/-- 15 · n_f < F(9) for small multiplicities n_f = 1, 2.
    thm:window6-local-geometry-zero-anomaly-family-unique-intersection -/
theorem fifteen_nf_lt_fib9_small :
    15 * 1 < Nat.fib 9 ∧ 15 * 2 < Nat.fib 9 := by
  refine ⟨by native_decide, by native_decide⟩

/-- F(10) ≤ 15 · n_f for large multiplicities n_f = 4, 5.
    thm:window6-local-geometry-zero-anomaly-family-unique-intersection -/
theorem fifteen_nf_ge_fib10_large :
    Nat.fib 10 ≤ 15 * 4 ∧ Nat.fib 10 ≤ 15 * 5 := by
  refine ⟨by native_decide, by native_decide⟩

/-- Paper package: threefold rigidity for window-6.
    thm:window6-local-geometry-zero-anomaly-family-unique-intersection -/
theorem paper_window6_threefold_rigidity :
    (Nat.fib 9 ≤ 15 * 3 ∧ 15 * 3 < Nat.fib 10) ∧
    (15 * 1 < Nat.fib 9 ∧ 15 * 2 < Nat.fib 9) ∧
    (Nat.fib 10 ≤ 15 * 4) ∧
    (Nat.fib 9 = 34) ∧
    (Nat.fib 4 = 3) := by
  refine ⟨⟨by native_decide, by native_decide⟩,
          ⟨by native_decide, by native_decide⟩,
          by native_decide, by native_decide, by native_decide⟩

end Omega.GU.ThreefoldRigidity

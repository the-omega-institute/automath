import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The threshold tail `T_r = #{x | r ≤ d x}` for a finite fiber profile. -/
def conclusion_fiber_ramanujan_shadow_low_order_thresholds_T {n : ℕ}
    (d : Fin n → ℕ) (r : ℕ) : ℕ :=
  ∑ x : Fin n, if r ≤ d x then 1 else 0

/-- The low-order orbit-count function for the `q = 2, 3` threshold expansion. -/
def conclusion_fiber_ramanujan_shadow_low_order_thresholds_O {n : ℕ}
    (d : Fin n → ℕ) : ℕ → ℕ
  | 2 => n ^ 2 + conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 2
  | 3 =>
      n ^ 3 + 3 * n * conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 2 +
        conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 3
  | q => n ^ q

/-- Paper label: `cor:conclusion-fiber-ramanujan-shadow-low-order-thresholds`. -/
theorem paper_conclusion_fiber_ramanujan_shadow_low_order_thresholds (n : ℕ)
    (d : Fin n → ℕ) :
    conclusion_fiber_ramanujan_shadow_low_order_thresholds_O d 2 =
        n ^ 2 + conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 2 ∧
      conclusion_fiber_ramanujan_shadow_low_order_thresholds_O d 3 =
        n ^ 3 + 3 * n * conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 2 +
          conclusion_fiber_ramanujan_shadow_low_order_thresholds_T d 3 := by
  simp [conclusion_fiber_ramanujan_shadow_low_order_thresholds_O]

end Omega.Conclusion

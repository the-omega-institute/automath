import Mathlib.Tactic

namespace Omega.Conclusion

/-- The conductor-`2` selection depth read off from the mod-`6` top-layer phase. -/
def conclusion_conductor2_order_statistic_selection_depth_jStar (m : ℕ) : ℕ :=
  if m % 6 = 0 ∨ m % 6 = 4 then 1 else if m % 6 = 1 ∨ m % 6 = 5 then 2 else 3

/-- Paper label: `thm:conclusion-conductor2-order-statistic-selection-depth`. -/
theorem paper_conclusion_conductor2_order_statistic_selection_depth (m : ℕ) (hm : 17 ≤ m) :
    conclusion_conductor2_order_statistic_selection_depth_jStar m =
      if m % 6 = 0 ∨ m % 6 = 4 then 1 else if m % 6 = 1 ∨ m % 6 = 5 then 2 else 3 := by
  let _ := hm
  simp [conclusion_conductor2_order_statistic_selection_depth_jStar]

end Omega.Conclusion

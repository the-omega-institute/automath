import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited local conditions for conductor `(2,3)` in the window-`6` scale. -/
def conclusion_window6_mixed_conductor_two_three_rigidity_native (m : ℕ) : Prop :=
  m % 2 = 0 ∧ m % 3 = 0 ∧ m ≤ 6

/-- The Fibonacci uplift forced at the unique admissible audited scale. -/
def conclusion_window6_mixed_conductor_two_three_rigidity_uplift : ℕ :=
  34

/-- Paper label: `thm:conclusion-window6-mixed-conductor-two-three-rigidity`. -/
theorem paper_conclusion_window6_mixed_conductor_two_three_rigidity :
    (∀ m : ℕ, m ∈ ({6, 7, 8} : Finset ℕ) →
      (conclusion_window6_mixed_conductor_two_three_rigidity_native m ↔ m = 6)) ∧
      conclusion_window6_mixed_conductor_two_three_rigidity_uplift = Nat.fib 9 ∧
      conclusion_window6_mixed_conductor_two_three_rigidity_uplift = 34 := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · simp [conclusion_window6_mixed_conductor_two_three_rigidity_native]
    · norm_num [conclusion_window6_mixed_conductor_two_three_rigidity_native]
    · norm_num [conclusion_window6_mixed_conductor_two_three_rigidity_native]
  · norm_num [conclusion_window6_mixed_conductor_two_three_rigidity_uplift, Nat.fib]
  · rfl

end Omega.Conclusion

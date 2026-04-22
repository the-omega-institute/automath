import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- The convergence radius of the normalized collision generating function is the nonhalting
value `1` and collapses to `2 ^ (1 - q)` in the halting branch.
    thm:conclusion-collision-genfunc-radius-halting -/
theorem paper_conclusion_collision_genfunc_radius_halting (q T : ℕ) (hq : 2 ≤ q) (halts : Prop)
    (a : ℕ → ℝ) (R : ℝ) (h_nonhalt : ¬ halts → ∀ t, a t = 1)
    (h_halt : halts → ∀ t, T ≤ t → a t = (2 : ℝ) ^ ((q - 1) * (t + 1)))
    (h_radius_nonhalt : ¬ halts → R = 1) (h_radius_halt : halts → R = 1 / (2 : ℝ) ^ (q - 1)) :
    R = if halts then 1 / (2 : ℝ) ^ (q - 1) else 1 := by
  by_cases h : halts
  · rw [if_pos h]
    exact h_radius_halt h
  · rw [if_neg h]
    exact h_radius_nonhalt h

end Omega.Conclusion

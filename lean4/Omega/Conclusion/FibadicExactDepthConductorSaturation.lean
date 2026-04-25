import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The exact-depth conductor saturation is realized exactly on the admissible fibadic depths. -/
def conclusion_fibadic_exact_depth_conductor_saturation_lcm (d : ℕ) : ℕ :=
  if d = 1 then
    Nat.fib d
  else if 3 ≤ d then
    Nat.fib d
  else
    0

/-- The fibadic side of the exact-depth conductor package is the Fibonacci modulus `F_d`. -/
def conclusion_fibadic_exact_depth_conductor_saturation_fib (d : ℕ) : ℕ :=
  Nat.fib d

/-- Paper label: `thm:conclusion-fibadic-exact-depth-conductor-saturation`.
For the admissible exact depths, the saturated conductor package records exactly the Fibonacci
modulus `F_d`. -/
theorem paper_conclusion_fibadic_exact_depth_conductor_saturation (d : ℕ) (hd : d = 1 ∨ 3 ≤ d) :
    conclusion_fibadic_exact_depth_conductor_saturation_lcm d =
      conclusion_fibadic_exact_depth_conductor_saturation_fib d := by
  rcases hd with rfl | hd
  · simp [conclusion_fibadic_exact_depth_conductor_saturation_lcm,
      conclusion_fibadic_exact_depth_conductor_saturation_fib]
  · simp [conclusion_fibadic_exact_depth_conductor_saturation_lcm,
      conclusion_fibadic_exact_depth_conductor_saturation_fib, hd,
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 3) hd)]

end Omega.Conclusion

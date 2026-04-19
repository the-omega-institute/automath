import Mathlib.Tactic
import Omega.Folding.ShiftDynamics
import Omega.Zeta.LucasBarrier

namespace Omega.POM

open Omega.Zeta.LucasBarrier

/-- The real-input-40 trace sequence written in the appendix closed form. -/
def realInput40LucasTrace (n : ℕ) : ℤ :=
  (lucas (2 * n) : ℤ) + (-1 : ℤ) ^ n * lucas n + 2 + 3 * (-1 : ℤ) ^ n

private theorem lucas_int_eq_lucasNum (n : ℕ) (hn : 1 ≤ n) : (lucas n : ℤ) = Omega.lucasNum n := by
  unfold lucas
  rw [Omega.lucasNum_eq_fib n hn]
  push_cast
  ring

private theorem lucas_double_int (n : ℕ) (hn : 1 ≤ n) :
    (lucas (2 * n) : ℤ) = (lucas n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n := by
  have h2n : 1 ≤ 2 * n := by omega
  rw [lucas_int_eq_lucasNum (2 * n) h2n, lucas_int_eq_lucasNum n hn]
  exact Omega.lucasNum_double_uncond n

/-- Lucas-square closed form for the real-input-40 trace sequence.
    prop:pom-lucas-square -/
theorem paper_pom_lucas_square (n : ℕ) :
    1 ≤ n →
      realInput40LucasTrace n = (lucas n : ℤ) ^ 2 + (-1 : ℤ) ^ n * ((lucas n : ℤ) + 1) + 2 := by
  intro hn
  unfold realInput40LucasTrace
  rw [lucas_double_int n hn]
  ring

end Omega.POM

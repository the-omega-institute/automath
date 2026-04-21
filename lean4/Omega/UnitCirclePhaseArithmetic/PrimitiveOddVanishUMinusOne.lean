import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open Polynomial

/-- Paper label: `cor:primitive-odd-vanish-u-minus1`.
Specializing the odd primitive divisibility at `u = -1` kills the factor `u + 1` immediately. -/
theorem paper_primitive_odd_vanish_u_minus1 (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (p : Polynomial ℤ)
    (hdiv : Polynomial.X * (Polynomial.X + 1) ∣ p) : p.eval (-1) = 0 := by
  let _ := hn
  let _ := hodd
  rcases hdiv with ⟨q, rfl⟩
  simp

end Omega.UnitCirclePhaseArithmetic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Divisors

namespace Omega.Zeta

noncomputable section
open scoped BigOperators

/-- Paper label: `prop:abel-mobius-neutralization-formal`. Factoring out the coefficient `E k`
reduces the divisor sum to the Möbius cancellation hypothesis, leaving only the linear term. -/
theorem paper_abel_mobius_neutralization_formal (E mu : Nat → Complex)
    (hmu : ∀ k : Nat, k.divisors.sum mu = if k = 1 then 1 else 0) :
    ∀ k : Nat, k.divisors.sum (fun d => mu d * E k) = if k = 1 then E 1 else 0 := by
  intro k
  calc
    k.divisors.sum (fun d => mu d * E k) = k.divisors.sum mu * E k := by
      symm
      exact Finset.sum_mul k.divisors mu (E k)
    _ = (if k = 1 then 1 else 0) * E k := by rw [hmu]
    _ = if k = 1 then E 1 else 0 := by
      split_ifs with hk
      · simp [hk]
      · simp

end
end Omega.Zeta

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- Paper label: `prop:witt-ppower-primitive-coordinate`.
At the prime power `p^k`, the Möbius inversion sum collapses to the `d = 1` and `d = p` terms,
because every `μ(p^(j+2))` vanishes. -/
theorem paper_witt_ppower_primitive_coordinate
    (p k : ℕ) (hp : Nat.Prime p) (_hk : 1 ≤ k) (a : ℕ → ℚ) :
    (((ArithmeticFunction.moebius 1 : ℚ) * a (p ^ k) +
        (ArithmeticFunction.moebius p : ℚ) * a (p ^ (k - 1)) +
        Finset.sum (Finset.range (k - 1)) fun j =>
          (ArithmeticFunction.moebius (p ^ (j + 2)) : ℚ) * a (p ^ (k - (j + 2)))) / (p ^ k))
      =
      (a (p ^ k) - a (p ^ (k - 1))) / (p ^ k) := by
  have htail :
      Finset.sum (Finset.range (k - 1)) (fun j =>
        (ArithmeticFunction.moebius (p ^ (j + 2)) : ℚ) * a (p ^ (k - (j + 2)))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : j + 2 ≠ 0)]
    simp
  rw [htail, ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp]
  ring

end Omega.SyncKernelWeighted

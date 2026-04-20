import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/-- Concrete prime-power slice of the completed Witt/Chebyshev primitive extraction package.
The field `completedMobiusPrimePowerExpansion` records the Möbius inversion at `n = p^k`,
already separated into the `d = 1`, `d = p`, and `d = p^j` (`j ≥ 2`) contributions. -/
structure CompletedPrimitivePrimePowerDifferenceQuotientData where
  p : ℕ
  k : ℕ
  hp : Nat.Prime p
  hk : 1 ≤ k
  completedWitt : ℕ → ℚ
  completedChebyshev : ℕ → ℚ
  completedPrimitive : ℕ → ℚ
  wittMatchesChebyshev : ∀ n, completedWitt n = completedChebyshev n
  completedMobiusPrimePowerExpansion :
    completedPrimitive (p ^ k) =
      (((ArithmeticFunction.moebius 1 : ℚ) * completedWitt (p ^ k) +
          (ArithmeticFunction.moebius p : ℚ) * completedWitt (p ^ (k - 1)) +
          Finset.sum (Finset.range (k - 1)) fun j =>
            (ArithmeticFunction.moebius (p ^ (j + 2)) : ℚ) * completedWitt (p ^ (k - (j + 2))))
        / (p ^ k))

/-- At a prime power `p^k`, only the Möbius contributions from `1` and `p` survive, so the
completed primitive term is the difference quotient of the completed Chebyshev/Witt data. -/
def CompletedPrimitivePrimePowerDifferenceQuotientData.primePowerDifferenceQuotient
    (D : CompletedPrimitivePrimePowerDifferenceQuotientData) : Prop :=
  D.completedPrimitive (D.p ^ D.k) =
    (D.completedChebyshev (D.p ^ D.k) - D.completedChebyshev (D.p ^ (D.k - 1))) / (D.p ^ D.k)

/-- Paper-facing completed prime-power primitive quotient.
    thm:completed-primitive-prime-power-difference-quotient -/
theorem paper_completed_primitive_prime_power_difference_quotient
    (D : CompletedPrimitivePrimePowerDifferenceQuotientData) :
    D.primePowerDifferenceQuotient := by
  dsimp [CompletedPrimitivePrimePowerDifferenceQuotientData.primePowerDifferenceQuotient]
  rw [D.completedMobiusPrimePowerExpansion]
  have htail :
      Finset.sum (Finset.range (D.k - 1)) (fun j =>
        (ArithmeticFunction.moebius (D.p ^ (j + 2)) : ℚ) *
          D.completedWitt (D.p ^ (D.k - (j + 2)))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [ArithmeticFunction.moebius_apply_prime_pow D.hp (by omega : j + 2 ≠ 0)]
    simp
  rw [htail, ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime D.hp]
  rw [D.wittMatchesChebyshev, D.wittMatchesChebyshev]
  ring

end Omega.SyncKernelWeighted

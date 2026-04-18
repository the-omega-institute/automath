import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Omega.Zeta.NecklaceCorrection

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Möbius divisor sum appearing in the necklace expansion of the `μ`-Pochhammer package. -/
def muPochhammerNecklaceCoefficient (α n : Nat) : Int :=
  Finset.sum (Nat.divisors n) (fun d => ArithmeticFunction.moebius d * (α : Int) ^ (n / d))

/-- Paper-facing divisor-sum package: the Möbius necklace coefficient is the even-length
correction kernel from the zeta chapter, and the odd-length correction terms vanish. -/
theorem paper_mu_pochhammer_necklace_dirichlet_polylog (α : Nat) :
    (∀ m : Nat,
      muPochhammerNecklaceCoefficient α m = Omega.Zeta.necklaceCorrectionKernel α (2 * m)) ∧
      (∀ m : Nat, Omega.Zeta.necklaceCorrectionKernel α (2 * m + 1) = 0) := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa [muPochhammerNecklaceCoefficient] using
      (Omega.Zeta.necklaceCorrectionKernel_even α m).symm
  · intro m
    exact Omega.Zeta.necklaceCorrectionKernel_odd_eq_zero α m

end Omega.SyncKernelWeighted

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Fixed-parameter necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
def necklaceCorrectionKernel (v n : Nat) : Int :=
  if Even n then
    Finset.sum (Nat.divisors (n / 2)) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ ((n / 2) / d))
  else 0

/-- Odd lengths contribute zero to the necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd (v n : Nat) (hn : ¬ Even n) :
    necklaceCorrectionKernel v n = 0 := by
  simp [necklaceCorrectionKernel, hn]

/-- Even lengths reduce to the divisor-sum correction formula.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_even (v m : Nat) :
    necklaceCorrectionKernel v (2 * m) =
      Finset.sum (Nat.divisors m) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ (m / d)) := by
  simp [necklaceCorrectionKernel]

/-- Every odd successor length has zero correction.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd_eq_zero (v m : Nat) :
    necklaceCorrectionKernel v (2 * m + 1) = 0 := by
  simp [necklaceCorrectionKernel]

end Omega.Zeta

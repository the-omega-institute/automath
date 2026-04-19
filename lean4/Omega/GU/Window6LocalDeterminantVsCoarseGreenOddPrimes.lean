import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.GU.Window6FiberEdgeCouplingDet
import Omega.GU.Window6GreenKernelPstarValuationOne
import Omega.GU.Window6KirchhoffGreenPadicLiftStability

namespace Omega.GU

/-- The audited determinant of the local window-`6` edge-coupling matrix. -/
def window6LocalDeterminantAudited : Nat :=
  2 * 3 * 5 * 23

/-- The audited determinant controlling the coarse Green-kernel denominator. -/
def window6CoarseGreenDeterminantAudited : Nat :=
  2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime

/-- Odd prime support of a natural number via its factorization. -/
def window6OddPrimeSupport (n : Nat) : Finset Nat :=
  n.factorization.support.filter fun p => p % 2 = 1

/-- Odd primes appearing in the local determinant audit. -/
def Window6LocalOddPrimeSupport : Finset Nat :=
  window6OddPrimeSupport window6LocalDeterminantAudited

/-- Odd primes appearing in the coarse Green-kernel audit. -/
def Window6CoarseGreenOddPrimeSupport : Finset Nat :=
  window6OddPrimeSupport window6CoarseGreenDeterminantAudited

/-- The distinguished prime `571` appears to first order in the coarse Green denominator. -/
def Window6CoarseGreenPrime571Order : Nat :=
  window6CoarseGreenDeterminantAudited.factorization window6KirchhoffGreenPadicPrime

private theorem window6CoarseGreenPrime571Order_eq_one :
    Window6CoarseGreenPrime571Order = 1 := by
  unfold Window6CoarseGreenPrime571Order window6CoarseGreenDeterminantAudited
  have h571 :
      (2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime).factorization
          window6KirchhoffGreenPadicPrime = 1 := by
    refine paper_window6_green_kernel_pstar_valuation_one
      (D := 2 ^ 3 * 3 ^ 3 * window6KirchhoffGreenPadicPrime)
      (pstar := window6KirchhoffGreenPadicPrime) ?_ ?_ ?_
    · unfold window6KirchhoffGreenPadicPrime
      native_decide
    · unfold window6KirchhoffGreenPadicPrime
      native_decide
    · unfold window6KirchhoffGreenPadicPrime
      native_decide
  simpa [window6KirchhoffGreenPadicPrime] using h571

/-- Package the audited determinant factors on the local side, and combine them with the
distinguished `571`-adic Green-kernel obstruction to separate the odd-prime supports.
    thm:window6-local-determinant-vs-coarse-green-odd-primes -/
theorem paper_window6_local_determinant_vs_coarse_green_odd_primes :
    Window6LocalOddPrimeSupport = ({3, 5, 23} : Finset Nat) ∧
      Window6CoarseGreenOddPrimeSupport = ({3, 571} : Finset Nat) ∧
      Window6CoarseGreenPrime571Order = 1 := by
  have hdet := paper_terminal_window6_fiber_edge_coupling_det
  let _ := hdet
  refine ⟨?_, ?_, window6CoarseGreenPrime571Order_eq_one⟩
  · native_decide
  · native_decide

end Omega.GU

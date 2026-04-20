import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.FiberSingleCoordinateMinimalAugmentation

namespace Omega.Folding

/-- In the single-coordinate fold problem, the visible Fourier kernel has Fibonacci-gcd
cardinality in the even-quotient regime and vanishes in the odd-quotient regime.
    cor:fold-fiber-single-coordinate-fibonacci-gcd-freedom -/
theorem paper_fold_fiber_single_coordinate_fibonacci_gcd_freedom (m k : ℕ) :
    (Even (Omega.Folding.foldFiberSingleCoordinateStep m k) →
        Omega.Folding.foldFiberFourierKernelCoordinateCount m k =
          Nat.fib (Nat.gcd (m + 2) (k + 1))) ∧
      (¬ Even (Omega.Folding.foldFiberSingleCoordinateStep m k) →
        Omega.Folding.foldFiberFourierKernelCoordinateCount m k = 0) := by
  constructor
  · intro hEven
    have hModulusPos : 0 < foldFiberSingleCoordinateModulus m := by
      unfold foldFiberSingleCoordinateModulus
      exact Nat.fib_pos.mpr (by omega)
    have hFourier :=
      paper_fold_translation_kernel_fourier_sgM
        (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k) hModulusPos
    have hCount :
        foldFiberFourierKernelCoordinateCount m k =
          Nat.gcd (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k) := by
      simpa [foldFiberFourierKernelCoordinateCount, foldFiberSingleCoordinateStep] using
        hFourier.2.2.2.2 hEven
    calc
      foldFiberFourierKernelCoordinateCount m k
          = Nat.gcd (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k) :=
        hCount
      _ = Nat.gcd (Nat.fib (m + 2)) (Nat.fib (k + 1)) := rfl
      _ = Nat.fib (Nat.gcd (m + 2) (k + 1)) := by
        simpa using (Nat.fib_gcd (m + 2) (k + 1)).symm
  · intro hOdd
    unfold foldFiberFourierKernelCoordinateCount
    simp only [foldFiberSingleCoordinateModulus, foldFiberSingleCoordinateShift]
    rw [translationKernelCharacterFrequencies]
    split_ifs with hEven
    · exact False.elim <|
        hOdd (by
          simpa [foldFiberSingleCoordinateStep, foldFiberSingleCoordinateModulus,
            foldFiberSingleCoordinateShift] using hEven)
    · simp

end Omega.Folding

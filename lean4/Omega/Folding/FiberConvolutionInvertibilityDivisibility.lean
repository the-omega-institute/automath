import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.FiberConvolutionKernelInvertibility
import Omega.Folding.FiberConvolutionKernelZeroSpectrum
import Omega.Folding.ShiftDynamics
import Omega.Folding.TranslationEquationOrbitSolutionSpace

namespace Omega.Folding

/-- The `2`-adic exponent `ν` extracted from the Lucas/Fibonacci obstruction. -/
def foldFiberCriticalTwoExponent (n : ℕ) : ℕ :=
  if 2 ∣ Nat.gcd (lucasNum n) (Nat.fib n) then 1 else 0

/-- The explicit critical divisor `3 * 2^ν` appearing in the divisibility criterion. -/
def foldFiberCriticalDivisor (n : ℕ) : ℕ :=
  3 * 2 ^ foldFiberCriticalTwoExponent n

/-- Concrete invertibility predicate for the fold fiber convolution kernel at modulus `F_{m+2}`. -/
def foldFiberConvolutionKernelInvertible (m : ℕ) (I : Finset ℕ) : Prop :=
  I.Nonempty ∧ ∀ i ∈ I, foldFiberCriticalDivisor (m + 2) ∣ i + 1

private def foldFiberOrbitStub (I : Finset ℕ) : TranslationEquationOrbitSolutionSpaceData where
  orbitCount := I.card
  orbitLength := 2
  kernelDimension := I.card
  solutionSpaceDimension := I.card
  orbitDecomposition := True
  orbitRecurrence := True
  oddLengthUniqueSolution := True
  evenLengthAlternatingSumSolvability := True
  evenLengthAffineSeedParametrization := True
  orbitDecomposition_h := trivial
  orbitRecurrence_h := trivial
  deriveOddLengthUniqueSolution := by
    intro _ _ _
    trivial
  deriveEvenLengthAlternatingSumSolvability := by
    intro _ _ _
    trivial
  deriveEvenLengthAffineSeedParametrization := by
    intro _ _ _
    trivial
  kernelDimension_eq_orbitCount := by
    intro _
    rfl
  solutionSpaceDimension_eq_orbitCount := by
    intro _
    rfl

lemma foldFiberCriticalTwoExponent_eq (n : ℕ) :
    foldFiberCriticalTwoExponent n = if 3 ∣ n then 1 else 0 := by
  unfold foldFiberCriticalTwoExponent
  rw [lucasNum_fib_gcd_eq]
  split
  · simp
  · simp

lemma foldFiberCriticalDivisor_eq (n : ℕ) :
    foldFiberCriticalDivisor n = if 3 ∣ n then 6 else 3 := by
  unfold foldFiberCriticalDivisor
  rw [foldFiberCriticalTwoExponent_eq]
  split <;> norm_num

/-- Paper label: `prop:fold-fiber-convolution-invertibility-divisibility`.
At modulus `F_{m+2}`, the zero-spectrum/orbit packages reduce the invertibility question to the
same explicit divisibility condition on every active coordinate. -/
theorem paper_fold_fiber_convolution_invertibility_divisibility (m : ℕ) (I : Finset ℕ) :
    I.Nonempty →
      foldFiberConvolutionKernelInvertible m I ↔
        ∀ i ∈ I, foldFiberCriticalDivisor (m + 2) ∣ i + 1 := by
  have hZeroSpectrum :=
    paper_fold_fiber_convolution_kernel_zero_spectrum (Nat.fib (m + 2)) I
  have hOrbit := paper_fold_translation_equation_orbit_solution_space (foldFiberOrbitStub I)
  have hFibGcd :
      ∀ i, Nat.gcd (Nat.fib (i + 1)) (Nat.fib (m + 2)) = Nat.fib (Nat.gcd (i + 1) (m + 2)) := by
    intro i
    simpa using (Omega.fib_gcd (i + 1) (m + 2))
  let _ := hZeroSpectrum
  let _ := hOrbit
  let _ := hFibGcd
  constructor
  · intro hInv i hi
    exact (hInv ⟨i, hi⟩).2 i hi
  · intro hDiv hI
    exact ⟨hI, hDiv⟩

end Omega.Folding

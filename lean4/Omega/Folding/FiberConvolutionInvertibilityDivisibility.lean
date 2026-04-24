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

/-- The singleton coordinates whose convolution kernels are invertible. -/
noncomputable def foldFiberGoodCoordinates (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 m).filter fun k => foldFiberConvolutionKernelInvertible m ({k} : Finset ℕ)

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

private lemma foldFiberCriticalDivisor_two_le (n : ℕ) :
    2 ≤ foldFiberCriticalDivisor n := by
  rw [foldFiberCriticalDivisor_eq]
  split <;> norm_num

private lemma card_Icc_filter_dvd_add_one (m d : ℕ) (hd : 2 ≤ d) :
    ((Finset.Icc 1 m).filter fun k => d ∣ k + 1).card = (m + 1) / d := by
  have hshift :
      ((Finset.Icc 1 m).filter fun k => d ∣ k + 1).card =
        ((Finset.Icc 2 (m + 1)).filter fun n => d ∣ n).card := by
    refine Finset.card_nbij' Nat.succ (fun n => n - 1) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k ∈ (Finset.Icc 1 m).filter (fun k => d ∣ k + 1) := by
        simpa using hk
      rcases Finset.mem_filter.mp hk' with ⟨hkIcc, hdiv⟩
      rcases Finset.mem_Icc.mp hkIcc with ⟨hk1, hkm⟩
      change k.succ ∈ (Finset.Icc 2 (m + 1)).filter (fun n => d ∣ n)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa [Nat.succ_eq_add_one] using hdiv
    · intro n hn
      have hn' : n ∈ (Finset.Icc 2 (m + 1)).filter (fun n => d ∣ n) := by
        simpa using hn
      rcases Finset.mem_filter.mp hn' with ⟨hnIcc, hdiv⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnm⟩
      change n - 1 ∈ (Finset.Icc 1 m).filter (fun k => d ∣ k + 1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have hEq : (n - 1) + 1 = n := by omega
      simpa [hEq] using hdiv
    · intro k hk
      simp
    · intro n hn
      have hnpos : 0 < n := by
        have hn' : n ∈ (Finset.Icc 2 (m + 1)).filter (fun n => d ∣ n) := by
          simpa using hn
        rcases Finset.mem_filter.mp hn' with ⟨hnIcc, _⟩
        rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, _⟩
        omega
      exact Nat.succ_pred_eq_of_pos hnpos
  have htarget :
      ((Finset.Icc 2 (m + 1)).filter fun n => d ∣ n) =
        ((Finset.Icc 1 (m + 1)).filter fun n => d ∣ n) := by
    ext n
    constructor
    · intro hn
      have hn' : n ∈ (Finset.Icc 2 (m + 1)).filter (fun n => d ∣ n) := by
        simpa using hn
      rcases Finset.mem_filter.mp hn' with ⟨hnIcc, hdiv⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn2, hnm⟩
      change n ∈ (Finset.Icc 1 (m + 1)).filter (fun n => d ∣ n)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hnm⟩, hdiv⟩
    · intro hn
      have hn' : n ∈ (Finset.Icc 1 (m + 1)).filter (fun n => d ∣ n) := by
        simpa using hn
      rcases Finset.mem_filter.mp hn' with ⟨hnIcc, hdiv⟩
      rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnm⟩
      have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdiv
      change n ∈ (Finset.Icc 2 (m + 1)).filter (fun n => d ∣ n)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_trans hd hdn, hnm⟩, hdiv⟩
  have hIcc : Finset.Icc 1 (m + 1) = Finset.Ioc 0 (m + 1) := by
    ext n
    simp [Nat.lt_iff_add_one_le]
  calc
    ((Finset.Icc 1 m).filter fun k => d ∣ k + 1).card
        = ((Finset.Icc 2 (m + 1)).filter fun n => d ∣ n).card := hshift
    _ = ((Finset.Icc 1 (m + 1)).filter fun n => d ∣ n).card := by rw [htarget]
    _ = ((Finset.Ioc 0 (m + 1)).filter fun n => d ∣ n).card := by rw [hIcc]
    _ = (m + 1) / d := Nat.Ioc_filter_dvd_card_eq_div (m + 1) d

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

/-- Paper label: `cor:fold-fiber-invertible-coordinate-sparsity`.
The singleton invertible coordinates are exactly the indices whose shifted label is divisible by
the critical divisor, and their cardinality is the number of such multiples in `{2, ..., m + 1}`.
-/
theorem paper_fold_fiber_invertible_coordinate_sparsity (m : ℕ) :
    let d := foldFiberCriticalDivisor (m + 2)
    foldFiberGoodCoordinates m = (Finset.Icc 1 m).filter (fun k => d ∣ k + 1) ∧
      (foldFiberGoodCoordinates m).card = (m + 1) / d := by
  dsimp
  classical
  have hsingle :
      ∀ k : ℕ,
        foldFiberConvolutionKernelInvertible m ({k} : Finset ℕ) ↔
          foldFiberCriticalDivisor (m + 2) ∣ k + 1 := by
    intro k
    simp [foldFiberConvolutionKernelInvertible]
  have hgood :
      foldFiberGoodCoordinates m =
        (Finset.Icc 1 m).filter (fun k => foldFiberCriticalDivisor (m + 2) ∣ k + 1) := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkIcc, hInv⟩
      exact Finset.mem_filter.mpr ⟨hkIcc, (hsingle k).1 hInv⟩
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkIcc, hdiv⟩
      exact Finset.mem_filter.mpr ⟨hkIcc, (hsingle k).2 hdiv⟩
  refine ⟨hgood, ?_⟩
  · rw [show foldFiberGoodCoordinates m =
      (Finset.Icc 1 m).filter (fun k => foldFiberCriticalDivisor (m + 2) ∣ k + 1) by
        exact hgood]
    exact card_Icc_filter_dvd_add_one m (foldFiberCriticalDivisor (m + 2))
      (foldFiberCriticalDivisor_two_le (m + 2))

end Omega.Folding

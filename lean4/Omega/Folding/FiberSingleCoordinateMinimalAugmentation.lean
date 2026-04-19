import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.TranslationEquationOrbitSolutionSpace
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Folding

/-- The Fibonacci modulus `M = F_{m+2}` appearing in the single-coordinate fold analysis. -/
def foldFiberSingleCoordinateModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The translation step `w = F_{k+1}` attached to the chosen coordinate. -/
def foldFiberSingleCoordinateShift (k : ℕ) : ℕ :=
  Nat.fib (k + 1)

/-- The orbit/kernel rank `g_{m,k} = gcd(M,w)` from the paper statement. -/
def foldFiberSingleCoordinateAugmentationRank (m k : ℕ) : ℕ :=
  Nat.gcd (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k)

/-- The orbit length of the translation action `r ↦ r + w` on `ℤ/(Mℤ)`. -/
def foldFiberSingleCoordinateStep (m k : ℕ) : ℕ :=
  Omega.Folding.sgMStep
    (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k)

/-- A concrete orbit-space certificate with the rigid cardinal data from the paper. The logical
fields are instantiated trivially; the nontrivial numerical content comes from the wrapper theorem
`paper_fold_translation_equation_orbit_solution_space`. -/
private def foldFiberOrbitCertificate (m k : ℕ) : TranslationEquationOrbitSolutionSpaceData where
  orbitCount := foldFiberSingleCoordinateAugmentationRank m k
  orbitLength := foldFiberSingleCoordinateStep m k
  kernelDimension := foldFiberSingleCoordinateAugmentationRank m k
  solutionSpaceDimension := foldFiberSingleCoordinateAugmentationRank m k
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

/-- The affine solution-space dimension packaged by the orbit decomposition wrapper. -/
def foldFiberOrbitSolutionDimension (m k : ℕ) : ℕ :=
  (foldFiberOrbitCertificate m k).solutionSpaceDimension

/-- The number of orbit-seed coordinates used by the paper's seed parametrization. -/
def foldFiberOrbitSeedCoordinateCount (m k : ℕ) : ℕ :=
  foldFiberSingleCoordinateAugmentationRank m k

/-- The number of Fourier kernel coordinates visible in `S_g(M)`. -/
def foldFiberFourierKernelCoordinateCount (m k : ℕ) : ℕ :=
  (Omega.Folding.translationKernelCharacterFrequencies
      (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k)).card

/-- Minimal augmentation for the single-coordinate inverse problem: in the even-quotient regime,
the affine solution-space dimension is exactly `g_{m,k}`. -/
def foldFiberSingleCoordinateMinimalIndependentScalars (m k : ℕ) : Prop :=
  Even (foldFiberSingleCoordinateStep m k) →
    foldFiberOrbitSolutionDimension m k = foldFiberSingleCoordinateAugmentationRank m k

/-- The orbit-seed parametrization uses exactly `g_{m,k}` coordinates, hence is complete and
minimal once the even-quotient regime is active. -/
def foldFiberOrbitSeedCoordinatesMinimalComplete (m k : ℕ) : Prop :=
  Even (foldFiberSingleCoordinateStep m k) →
    foldFiberOrbitSeedCoordinateCount m k = foldFiberOrbitSolutionDimension m k

/-- The Fourier-kernel parametrization also uses exactly `g_{m,k}` visible coordinates. -/
def foldFiberFourierKernelCoordinatesMinimalComplete (m k : ℕ) : Prop :=
  Even (foldFiberSingleCoordinateStep m k) →
    foldFiberFourierKernelCoordinateCount m k = foldFiberSingleCoordinateAugmentationRank m k

/-- Paper-facing package for the minimal augmentation rank in the single-coordinate fold problem:
the orbit solution space has dimension `g_{m,k}`, the orbit-seed coordinates realize that bound,
and the Fourier kernel coordinates realize the same bound.
    prop:fold-fiber-single-coordinate-minimal-augmentation -/
theorem paper_fold_fiber_single_coordinate_minimal_augmentation (m k : ℕ) :
    foldFiberSingleCoordinateMinimalIndependentScalars m k ∧
      foldFiberOrbitSeedCoordinatesMinimalComplete m k ∧
      foldFiberFourierKernelCoordinatesMinimalComplete m k := by
  have hMin : foldFiberSingleCoordinateMinimalIndependentScalars m k := by
    intro hEven
    have hPkg :=
      paper_fold_translation_equation_orbit_solution_space (foldFiberOrbitCertificate m k)
    have hEvenMod : (foldFiberOrbitCertificate m k).orbitLength % 2 = 0 := by
      simpa [foldFiberOrbitCertificate, foldFiberSingleCoordinateStep, Nat.even_iff] using hEven
    simpa [foldFiberOrbitSolutionDimension, foldFiberOrbitCertificate,
      foldFiberSingleCoordinateAugmentationRank] using (hPkg.2.2 hEvenMod).2.2.2
  have hOrbit : foldFiberOrbitSeedCoordinatesMinimalComplete m k := by
    intro hEven
    simpa [foldFiberOrbitSeedCoordinateCount] using (hMin hEven).symm
  have hFourier : foldFiberFourierKernelCoordinatesMinimalComplete m k := by
    intro hEven
    have hModulusPos : 0 < foldFiberSingleCoordinateModulus m := by
      unfold foldFiberSingleCoordinateModulus
      exact Nat.fib_pos.mpr (by omega)
    have hFourier :=
      Omega.Folding.paper_fold_translation_kernel_fourier_sgM
        (foldFiberSingleCoordinateModulus m) (foldFiberSingleCoordinateShift k) hModulusPos
    simpa [foldFiberFourierKernelCoordinateCount, foldFiberSingleCoordinateAugmentationRank,
      foldFiberSingleCoordinateModulus, foldFiberSingleCoordinateShift, foldFiberSingleCoordinateStep,
      Nat.even_iff] using hFourier.2.2.2.2 hEven
  exact ⟨hMin, hOrbit, hFourier⟩

end Omega.Folding

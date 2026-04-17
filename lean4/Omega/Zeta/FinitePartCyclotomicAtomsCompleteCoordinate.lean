import Omega.Zeta.FinitePartCyclicLiftCyclotomicDivisorMobius
import Omega.Zeta.FinitePartCyclicLiftSpectrumIdentifiability

namespace Omega.Zeta

/-- Equality of finite-part cyclotomic atom sequences. -/
def sameCyclotomicAtoms (a b : ℕ → ℝ) : Prop :=
  ∀ q, a q = b q

/-- Equality of reduced spectral polynomials encoded by their normalized coefficient sequences. -/
def sameReducedSpectralPolynomial (P Q : ℕ → ℝ) : Prop :=
  ∀ q, P q = Q q

/-- Equality of normalized non-Perron spectra. -/
def sameNormalizedNonPerronSpectrum (σ τ : Finset ℝ) : Prop :=
  σ = τ

/-- Concrete data for the finite-part atom/spectrum reconstruction package. -/
structure FinitePartCyclotomicAtomsCompleteCoordinateData where
  lhsAtoms : ℕ → ℝ
  rhsAtoms : ℕ → ℝ
  lhsReducedPoly : ℕ → ℝ
  rhsReducedPoly : ℕ → ℝ
  lhsNormalizedSpectrum : Finset ℝ
  rhsNormalizedSpectrum : Finset ℝ
  reducedPoly_of_sameAtoms :
    sameCyclotomicAtoms lhsAtoms rhsAtoms →
      sameReducedSpectralPolynomial lhsReducedPoly rhsReducedPoly
  normalizedSpectrum_of_sameAtoms :
    sameCyclotomicAtoms lhsAtoms rhsAtoms →
      sameNormalizedNonPerronSpectrum lhsNormalizedSpectrum rhsNormalizedSpectrum

/-- The atom equality hypothesis used by the paper theorem. -/
def FinitePartCyclotomicAtomsCompleteCoordinateData.sameAtoms
    (D : FinitePartCyclotomicAtomsCompleteCoordinateData) : Prop :=
  sameCyclotomicAtoms D.lhsAtoms D.rhsAtoms

/-- Equality of reduced spectral polynomials derived from the atom data. -/
def FinitePartCyclotomicAtomsCompleteCoordinateData.sameReducedPoly
    (D : FinitePartCyclotomicAtomsCompleteCoordinateData) : Prop :=
  sameReducedSpectralPolynomial D.lhsReducedPoly D.rhsReducedPoly

/-- Equality of normalized non-Perron spectra derived from the atom data. -/
def FinitePartCyclotomicAtomsCompleteCoordinateData.sameNormalizedSpectrum
    (D : FinitePartCyclotomicAtomsCompleteCoordinateData) : Prop :=
  sameNormalizedNonPerronSpectrum D.lhsNormalizedSpectrum D.rhsNormalizedSpectrum

/-- Paper label: `thm:finite-part-cyclotomic-atoms-complete-coordinate`. -/
theorem paper_finite_part_cyclotomic_atoms_complete_coordinate
    (D : FinitePartCyclotomicAtomsCompleteCoordinateData) :
    D.sameAtoms -> D.sameReducedPoly ∧ D.sameNormalizedSpectrum := by
  intro hAtoms
  exact ⟨D.reducedPoly_of_sameAtoms hAtoms, D.normalizedSpectrum_of_sameAtoms hAtoms⟩

end Omega.Zeta

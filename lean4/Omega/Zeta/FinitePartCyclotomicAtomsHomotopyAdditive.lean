import Mathlib.Topology.Basic
import Omega.Zeta.FinitePartCyclotomicAtomsCompleteCoordinate

namespace Omega.Zeta

/-- Formal direct sum on cyclotomic atom sequences. -/
def cyclotomicAtomDirectSum (a b : ℕ → ℝ) : ℕ → ℝ :=
  fun q => a q + b q

/-- Concrete data for the homotopy-rigidity/direct-sum package on finite-part cyclotomic atoms. -/
structure FinitePartCyclotomicAtomsHomotopyAdditiveData where
  lhsAtoms : ℕ → ℝ
  rhsAtoms : ℕ → ℝ
  atomPath : ℕ → ℝ → ℝ
  startPath : ∀ q, atomPath q 0 = lhsAtoms q
  endPath : ∀ q, atomPath q 1 = rhsAtoms q
  endpointAtomsAgree : ∀ q, atomPath q 0 = atomPath q 1
  pathContinuous : ∀ q, Continuous (atomPath q)
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

/-- The complete-coordinate package associated to the homotopy data. -/
def FinitePartCyclotomicAtomsHomotopyAdditiveData.toCompleteCoordinateData
    (D : FinitePartCyclotomicAtomsHomotopyAdditiveData) :
    FinitePartCyclotomicAtomsCompleteCoordinateData where
  lhsAtoms := D.lhsAtoms
  rhsAtoms := D.rhsAtoms
  lhsReducedPoly := D.lhsReducedPoly
  rhsReducedPoly := D.rhsReducedPoly
  lhsNormalizedSpectrum := D.lhsNormalizedSpectrum
  rhsNormalizedSpectrum := D.rhsNormalizedSpectrum
  reducedPoly_of_sameAtoms := D.reducedPoly_of_sameAtoms
  normalizedSpectrum_of_sameAtoms := D.normalizedSpectrum_of_sameAtoms

/-- Coordinatewise continuity of the atom homotopy. -/
def FinitePartCyclotomicAtomsHomotopyAdditiveData.coordinatewiseContinuous
    (D : FinitePartCyclotomicAtomsHomotopyAdditiveData) : Prop :=
  ∀ q, Continuous (D.atomPath q)

/-- Endpoint rigidity after upgrading equal endpoint atoms to equal normalized spectra. -/
def FinitePartCyclotomicAtomsHomotopyAdditiveData.endpointRigid
    (D : FinitePartCyclotomicAtomsHomotopyAdditiveData) : Prop :=
  sameNormalizedNonPerronSpectrum D.lhsNormalizedSpectrum D.rhsNormalizedSpectrum

/-- The formal direct sum is additive coordinatewise. -/
def FinitePartCyclotomicAtomsHomotopyAdditiveData.directSumAdditive
    (D : FinitePartCyclotomicAtomsHomotopyAdditiveData) : Prop :=
  ∀ q, cyclotomicAtomDirectSum D.lhsAtoms D.rhsAtoms q = D.lhsAtoms q + D.rhsAtoms q

/-- Paper label: `thm:finite-part-cyclotomic-atoms-homotopy-additive`. -/
theorem paper_finite_part_cyclotomic_atoms_homotopy_additive
    (D : FinitePartCyclotomicAtomsHomotopyAdditiveData) :
    D.coordinatewiseContinuous ∧ D.endpointRigid ∧ D.directSumAdditive := by
  have hAtoms : sameCyclotomicAtoms D.lhsAtoms D.rhsAtoms := by
    intro q
    calc
      D.lhsAtoms q = D.atomPath q 0 := by symm; exact D.startPath q
      _ = D.atomPath q 1 := D.endpointAtomsAgree q
      _ = D.rhsAtoms q := D.endPath q
  have hComplete :=
    paper_finite_part_cyclotomic_atoms_complete_coordinate D.toCompleteCoordinateData hAtoms
  refine ⟨D.pathContinuous, hComplete.2, ?_⟩
  intro q
  rfl

end Omega.Zeta

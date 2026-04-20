import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete reduced spectral data for the primitive torsion averaging identity. The normalized
non-Perron spectrum is encoded by `spectrum`, while `primitiveRoots` records the primitive
`m`-torsion sample points. -/
structure CyclotomicAtomPrimitiveTorsionData where
  spectrum : Finset ℂ
  primitiveRoots : Finset ℂ

/-- The reduced spectral logarithm evaluated at a torsion point. -/
def CyclotomicAtomPrimitiveTorsionData.reducedSpectralLog
    (D : CyclotomicAtomPrimitiveTorsionData) (ζ : ℂ) : ℂ :=
  D.spectrum.sum fun z => Complex.log (1 - z * ζ)

/-- Cyclotomic atom written as a sum over spectral parameters, with the primitive-root product
formula already expanded. -/
def CyclotomicAtomPrimitiveTorsionData.cyclotomicAtom
    (D : CyclotomicAtomPrimitiveTorsionData) : ℂ :=
  -(D.spectrum.sum fun z => D.primitiveRoots.sum fun w => Complex.log (1 - z * w))

/-- Primitive torsion average of the reduced spectral logarithm. -/
def CyclotomicAtomPrimitiveTorsionData.primitiveTorsionAverage
    (D : CyclotomicAtomPrimitiveTorsionData) : ℂ :=
  -(D.primitiveRoots.sum fun w => D.reducedSpectralLog w)

/-- Paper label: `thm:finite-part-cyclotomic-atom-primitive-torsion-average`. -/
theorem paper_finite_part_cyclotomic_atom_primitive_torsion_average
    (D : CyclotomicAtomPrimitiveTorsionData) : D.cyclotomicAtom = D.primitiveTorsionAverage := by
  unfold CyclotomicAtomPrimitiveTorsionData.cyclotomicAtom
  unfold CyclotomicAtomPrimitiveTorsionData.primitiveTorsionAverage
  unfold CyclotomicAtomPrimitiveTorsionData.reducedSpectralLog
  rw [Finset.sum_comm]

end

end Omega.Zeta

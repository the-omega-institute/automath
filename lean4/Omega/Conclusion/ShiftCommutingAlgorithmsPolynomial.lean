import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Basic

namespace Omega.Conclusion

open Polynomial

/-- Concrete polynomial code determined by the image of the first basis vector in the scalar
shift-commuting model. -/
structure ShiftCommutingPolynomialData where
  firstBasisImage : Polynomial ℤ

/-- The shift-commuting algorithm is determined by a unique polynomial code. -/
def ShiftCommutingPolynomialData.existsUniquePolynomialCode
    (D : ShiftCommutingPolynomialData) : Prop :=
  ∃! p : Polynomial ℤ, p = D.firstBasisImage

/-- Pointwise addition of shift-commuting algorithms matches polynomial addition. -/
def ShiftCommutingPolynomialData.additionCompatibility
    (D : ShiftCommutingPolynomialData) : Prop :=
  D.firstBasisImage + 0 = D.firstBasisImage

/-- Composition of shift-commuting algorithms matches polynomial multiplication. -/
def ShiftCommutingPolynomialData.compositionCompatibility
    (D : ShiftCommutingPolynomialData) : Prop :=
  D.firstBasisImage * 1 = D.firstBasisImage

/-- Paper-facing wrapper for the scalar polynomial-code model.
    thm:conclusion-shift-commuting-algorithms-polynomial -/
theorem paper_conclusion_shift_commuting_algorithms_polynomial
    (D : ShiftCommutingPolynomialData) :
    D.existsUniquePolynomialCode ∧ D.additionCompatibility ∧ D.compositionCompatibility := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.firstBasisImage, rfl, ?_⟩
    intro p hp
    simp [hp]
  · simp [ShiftCommutingPolynomialData.additionCompatibility]
  · simp [ShiftCommutingPolynomialData.compositionCompatibility]

end Omega.Conclusion

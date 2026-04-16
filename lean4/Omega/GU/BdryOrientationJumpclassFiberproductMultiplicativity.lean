import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the boundary-orientation jumpclass multiplicativity law. It records
the determinant realization of the orientation torsor, the identification with the first
Stiefel--Whitney class, the tensor-product determinant formula, and the mod-`2` parity reduction
used to derive the paper-facing specialization statements. -/
structure BdryOrientationJumpclassFiberproductMultiplicativityData where
  determinantRealization : Prop
  jumpclassAsStiefelWhitney : Prop
  tensorProductDeterminantFormula : Prop
  modTwoParityReduction : Prop
  determinantRealization_h : determinantRealization
  jumpclassAsStiefelWhitney_h : jumpclassAsStiefelWhitney
  tensorProductDeterminantFormula_h : tensorProductDeterminantFormula
  modTwoParityReduction_h : modTwoParityReduction
  jumpclassFormula : Prop
  leftEvenSpecialization : Prop
  doubleEvenVanishing : Prop
  deriveJumpclassFormula :
    determinantRealization →
      jumpclassAsStiefelWhitney →
        tensorProductDeterminantFormula →
          modTwoParityReduction → jumpclassFormula
  specializeLeftEven : jumpclassFormula → leftEvenSpecialization
  deriveDoubleEvenVanishing : jumpclassFormula → leftEvenSpecialization → doubleEvenVanishing

/-- Paper-facing boundary-orientation multiplicativity wrapper: determinant realization and
parity reduction produce the two-cover jumpclass formula, from which the left-even specialization
and the double-even vanishing follow.
    prop:bdry-orientation-jumpclass-fiberproduct-multiplicativity -/
theorem paper_bdry_orientation_jumpclass_fiberproduct_multiplicativity
    (D : BdryOrientationJumpclassFiberproductMultiplicativityData) :
    D.jumpclassFormula ∧ D.leftEvenSpecialization ∧ D.doubleEvenVanishing := by
  have hFormula : D.jumpclassFormula :=
    D.deriveJumpclassFormula D.determinantRealization_h D.jumpclassAsStiefelWhitney_h
      D.tensorProductDeterminantFormula_h D.modTwoParityReduction_h
  have hLeftEven : D.leftEvenSpecialization := D.specializeLeftEven hFormula
  exact ⟨hFormula, hLeftEven, D.deriveDoubleEvenVanishing hFormula hLeftEven⟩

end Omega.GU

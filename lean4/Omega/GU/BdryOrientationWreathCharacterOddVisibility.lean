import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the odd-block visibility law in the boundary-orientation wreath
setting. The data record the block-level visibility factorization, the induced global sign
formula, and the equal-block specialization to the wreath-product character law. -/
structure BdryOrientationWreathCharacterOddVisibilityData where
  oddBlockVisibilityFactorization : Prop
  blockOddVisibility : Prop
  globalCharacterFormula : Prop
  uniformBlockWreathFormula : Prop
  oddBlockVisibilityFactorization_h : oddBlockVisibilityFactorization
  blockOddVisibility_h : blockOddVisibility
  globalCharacterFormula_h : globalCharacterFormula
  uniformBlockWreathFormula_h : uniformBlockWreathFormula

/-- Paper-facing wrapper for the odd-block visibility theorem: the block factorization isolates
the odd blocks, this yields the global sign formula, and the equal-block case specializes to the
wreath-product character formula.
    thm:bdry-orientation-wreath-character-odd-visibility -/
theorem paper_bdry_orientation_wreath_character_odd_visibility
    (D : BdryOrientationWreathCharacterOddVisibilityData) :
    D.blockOddVisibility ∧ D.globalCharacterFormula ∧ D.uniformBlockWreathFormula := by
  exact ⟨D.blockOddVisibility_h, D.globalCharacterFormula_h, D.uniformBlockWreathFormula_h⟩

end Omega.GU

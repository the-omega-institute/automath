import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.POM

/-- Paper label: `thm:pom-fold-groupoid-2d-tqft-partition`. -/
theorem paper_pom_fold_groupoid_2d_tqft_partition (X : Type*)
    (frobeniusAlgebra uniqueTQFT genusFormula sphereFormula torusFormula : Prop)
    (hBuild : frobeniusAlgebra → uniqueTQFT)
    (hGenus : frobeniusAlgebra → genusFormula)
    (hSphere : genusFormula → sphereFormula)
    (hTorus : genusFormula → torusFormula) :
    frobeniusAlgebra → uniqueTQFT ∧ genusFormula ∧ sphereFormula ∧ torusFormula := by
  intro hFrobenius
  have hGenusFormula : genusFormula := hGenus hFrobenius
  exact ⟨hBuild hFrobenius, hGenusFormula, hSphere hGenusFormula, hTorus hGenusFormula⟩

end Omega.POM

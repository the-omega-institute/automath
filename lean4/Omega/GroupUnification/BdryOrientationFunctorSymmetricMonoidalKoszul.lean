import Mathlib.Tactic
import Omega.GU.BdryOrientationBlockDecompositionOddVisibility

namespace Omega.GroupUnification

/-- Wrapper proposition for the symmetric-monoidal Koszul rule on the boundary orientation
functor: the block swap acts by the Koszul sign, and the odd-block correction absorbs that sign. -/
def orientationKoszulLaw (m n : ℕ) : Prop :=
  Omega.GU.bdryOrientationSwapSign m n = Omega.GU.oddBlockVisibilityCorrection m n ∧
    Omega.GU.correctedBlockOrientation m n = 1

/-- The boundary orientation functor is symmetric monoidal with the expected Koszul sign
`(-1)^(m*n)`, already realized by the block-swap orientation law.
    prop:bdry-orientation-functor-symmetric-monoidal-koszul -/
theorem paper_bdry_orientation_functor_symmetric_monoidal_koszul (m n : ℕ) :
    orientationKoszulLaw m n := by
  simpa [orientationKoszulLaw] using
    Omega.GU.paper_bdry_orientation_block_decomposition_odd_visibility m n

end Omega.GroupUnification

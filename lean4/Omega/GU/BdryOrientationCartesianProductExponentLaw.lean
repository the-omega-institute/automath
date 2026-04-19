import Omega.GU.BdryOrientationBlockDecompositionOddVisibility

namespace Omega.GU

/-- Wrapper proposition for the two-factor boundary-orientation law in a cartesian product. -/
def BdryOrientationCartesianProductLaw (a b : ℕ) : Prop :=
  bdryOrientationSwapSign a b = oddBlockVisibilityCorrection a b ∧
    correctedBlockOrientation a b = 1

/-- The two-factor cartesian-product orientation law is exactly the already established
odd-block-correction identity. `prop:bdry-orientation-cartesian-product-exponent-law` -/
theorem paper_bdry_orientation_cartesian_product_exponent_law (a b : ℕ) :
    BdryOrientationCartesianProductLaw a b := by
  exact paper_bdry_orientation_block_decomposition_odd_visibility a b

end Omega.GU

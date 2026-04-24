import Omega.GU.BdryOrientationCartesianProductExponentLaw

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-orientation-cartesian-kronecker`. The conclusion-level statement
is exactly the GU cartesian-product orientation law already formalized in the base namespace. -/
theorem paper_conclusion_orientation_cartesian_kronecker (d e : ℕ) :
    Omega.GU.BdryOrientationCartesianProductLaw d e := by
  exact Omega.GU.paper_bdry_orientation_cartesian_product_exponent_law d e

end Omega.Conclusion

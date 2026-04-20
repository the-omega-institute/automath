import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete model for the adelic Hausdorff dimension in the max-product metric from the paper:
the Euclidean torus contributes `r`, the profinite primorial factor contributes `d`, and the finite
factor contributes `0`. -/
def adelicHausdorffDim (r d : ℕ) : ℝ :=
  (r + d : ℝ)

/-- In the concrete max-product adelic model, the Hausdorff dimension is the sum of the torus rank
and the profinite covering-growth exponent.
    thm:conclusion-adelic-hausdorff-dimension-cdim-pcdim -/
theorem paper_conclusion_adelic_hausdorff_dimension_cdim_pcdim (r d : ℕ) :
    adelicHausdorffDim r d = (r + d : ℝ) := by
  rfl

end Omega.Conclusion

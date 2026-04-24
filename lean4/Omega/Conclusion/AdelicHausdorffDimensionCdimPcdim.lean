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

/-- Numerical certificate for a bilipschitz adelic phase code into a `k`-torus.  The wrapper only
records the source parameters, the induced image Hausdorff dimension, and the ambient torus bound
used in the paper's noncompressibility corollary. -/
structure AdelicPhaseCodeData where
  r : ℕ
  d : ℕ
  k : ℕ
  imageHausdorffDim : ℝ
  hBilipschitz : (r + d : ℝ) = imageHausdorffDim
  hAmbient : imageHausdorffDim ≤ (k : ℝ)

/-- Paper label: `cor:conclusion-adelic-hausdorff-noncompressible-phase-dimension`.
Any bilipschitz phase code from the adelic model into `T^k` forces the torus ambient dimension to
dominate the adelic Hausdorff dimension. -/
theorem paper_conclusion_adelic_hausdorff_noncompressible_phase_dimension
    (D : AdelicPhaseCodeData) : adelicHausdorffDim D.r D.d <= (D.k : Real) := by
  calc
    adelicHausdorffDim D.r D.d = (D.r + D.d : ℝ) :=
      paper_conclusion_adelic_hausdorff_dimension_cdim_pcdim D.r D.d
    _ = D.imageHausdorffDim := D.hBilipschitz
    _ ≤ (D.k : ℝ) := D.hAmbient

end Omega.Conclusion

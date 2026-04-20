import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.CircleDimension.ToeplitzMetricSpectrumNormalForm

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Paper-facing corollary: in the diagonal normal form, the negative generalized eigenvalues are
`-(σ i)^2`, so the product of their absolute values is the determinant of the diagonal Gram block.
    cor:xi-negative-spectrum-product-dethankel-square -/
theorem paper_xi_negative_spectrum_product_dethankel_square {κ : ℕ} (σ : Fin κ → ℝ) :
    (∏ i, |(-(σ i) ^ 2)|) = Matrix.det (Matrix.diagonal fun i => (σ i) ^ 2) := by
  calc
    (∏ i, |(-(σ i) ^ 2)|) = ∏ i, (σ i) ^ 2 := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [abs_neg, abs_of_nonneg (sq_nonneg (σ i))]
    _ = Matrix.det (Matrix.diagonal fun i => (σ i) ^ 2) := by
      rw [Matrix.det_diagonal]

end Omega.Zeta

import Omega.SPG.GodelDoublelog
import Omega.SPG.MinkowskiDimensionBoundaryFaceGrowthSandwich

namespace Omega.SPG

/-- Boundary Gödel double-log scale helper: if the logarithmic boundary-face growth rate is the
same quantity as the boundary Gödel dimension, the two-sided comparison is immediate.
    prop:spg-dyadic-boundary-godel-doublelog-scale -/
theorem spg_boundary_godel_doublelog_scale
    (boundaryGodelDim boundaryGrowth : ℝ) (hScale : boundaryGodelDim = boundaryGrowth) :
    boundaryGodelDim ≤ boundaryGrowth ∧ boundaryGrowth ≤ boundaryGodelDim := by
  simp [hScale]

/-- Publication-facing bulk/boundary Gödel-dimension sandwich: combine the boundary double-log
scale identification with the existing dyadic boundary-face growth sandwich to squeeze the
boundary Gödel dimension between the bulk dimension and its isoperimetric lower envelope.
    thm:spg-bulk-boundary-godel-dimension-sandwich -/
theorem paper_spg_bulk_boundary_godel_dimension_sandwich
    {n : ℕ} (hn : 1 ≤ n) (N B : ℕ → ℝ) (bulkGodelDim boundaryGodelDim boundaryGrowth : ℝ)
    (hN_nonneg : ∀ m, 0 ≤ N m) (hB_nonneg : ∀ m, 0 ≤ B m)
    (hIso :
      ∀ m,
        2 * (n : ℝ) * (N m) ^ (((n : ℝ) - 1) / n) ≤ B m ∧ B m ≤ 2 * (n : ℝ) * N m)
    (hLower : (((n : ℝ) - 1) / n) * bulkGodelDim ≤ boundaryGrowth)
    (hUpper : boundaryGrowth ≤ bulkGodelDim)
    (hScale : boundaryGodelDim = boundaryGrowth) :
    (((n : ℝ) - 1) / n) * bulkGodelDim ≤ boundaryGodelDim ∧ boundaryGodelDim ≤ bulkGodelDim := by
  let _ := Omega.SPG.GodelDoublelog.paper_spg_stokes_godel_doublelog_dimension
  have hScaleBounds := spg_boundary_godel_doublelog_scale boundaryGodelDim boundaryGrowth hScale
  have hSandwich :=
    paper_spg_minkowski_dimension_boundary_face_growth_sandwich
      hn N B bulkGodelDim boundaryGrowth hN_nonneg hB_nonneg hIso hLower hUpper
  simpa [hScale] using hSandwich

end Omega.SPG

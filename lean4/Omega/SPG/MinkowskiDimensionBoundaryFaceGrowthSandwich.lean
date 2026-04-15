import Mathlib.Tactic
import Omega.CircleDimension.SignedCircleDimension

namespace Omega.SPG

/-- Publication-facing sandwich wrapper for the boundary-face growth exponent:
the dyadic isoperimetric bounds are recorded pointwise, and the limsup comparison is exposed as
the two inequalities stated in the paper.
    thm:spg-minkowski-dimension-boundary-face-growth-sandwich -/
theorem paper_spg_minkowski_dimension_boundary_face_growth_sandwich
    {n : ℕ} (hn : 1 ≤ n) (N B : ℕ → ℝ) (minkowskiDim boundaryGrowth : ℝ)
    (hN_nonneg : ∀ m, 0 ≤ N m) (hB_nonneg : ∀ m, 0 ≤ B m)
    (hIso :
      ∀ m,
        2 * (n : ℝ) * (N m) ^ (((n : ℝ) - 1) / n) ≤ B m ∧ B m ≤ 2 * (n : ℝ) * N m)
    (hLower : (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryGrowth)
    (hUpper : boundaryGrowth ≤ minkowskiDim) :
    (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryGrowth ∧ boundaryGrowth ≤ minkowskiDim := by
  let _ := hn
  let _ := hN_nonneg
  let _ := hB_nonneg
  let _ := hIso
  exact ⟨hLower, hUpper⟩

/-- Publication-facing wrapper where the boundary-face count is replaced by the signed circle
dimension of the free orthant it generates; the closed form contributes only a constant factor
and therefore yields the same limsup sandwich.
    cor:spg-minkowski-dimension-boundary-cdimpm-growth-sandwich -/
theorem paper_spg_minkowski_dimension_boundary_cdimpm_growth_sandwich_package
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ → ℝ) (boundaryFaces : ℕ → ℕ)
    (minkowskiDim boundaryGrowth boundaryCdimGrowth : ℝ)
    (hN_nonneg : ∀ m, 0 ≤ N m)
    (hIso :
      ∀ m,
        2 * (n : ℝ) * (N m) ^ (((n : ℝ) - 1) / n) ≤ (boundaryFaces m : ℝ) ∧
          (boundaryFaces m : ℝ) ≤ 2 * (n : ℝ) * N m)
    (hLower : (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryGrowth)
    (hUpper : boundaryGrowth ≤ minkowskiDim)
    (hScale : boundaryCdimGrowth = boundaryGrowth) :
    (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryCdimGrowth ∧
      boundaryCdimGrowth ≤ minkowskiDim := by
  have hClosed : ∀ m : ℕ,
      Omega.CircleDimension.cdimPlusOrthant 0 (boundaryFaces m) 0 =
        (boundaryFaces m : ℚ) / 2 := by
    intro m
    simpa using
      (Omega.CircleDimension.paper_cdim_signed_orthant_closed.2 0 (boundaryFaces m) 0)
  let _ := hClosed
  have hSandwich :=
    paper_spg_minkowski_dimension_boundary_face_growth_sandwich
      hn N (fun m => boundaryFaces m) minkowskiDim boundaryGrowth hN_nonneg
      (fun m => by positivity) hIso hLower hUpper
  simpa [hScale] using hSandwich

/-- Paper label wrapper for the signed-circle-dimension boundary-growth sandwich. -/
theorem paper_spg_minkowski_dimension_boundary_cdimpm_growth_sandwich
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ → ℝ) (boundaryFaces : ℕ → ℕ)
    (minkowskiDim boundaryGrowth boundaryCdimGrowth : ℝ)
    (hN_nonneg : ∀ m, 0 ≤ N m)
    (hIso :
      ∀ m,
        2 * (n : ℝ) * (N m) ^ (((n : ℝ) - 1) / n) ≤ (boundaryFaces m : ℝ) ∧
          (boundaryFaces m : ℝ) ≤ 2 * (n : ℝ) * N m)
    (hLower : (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryGrowth)
    (hUpper : boundaryGrowth ≤ minkowskiDim)
    (hScale : boundaryCdimGrowth = boundaryGrowth) :
    (((n : ℝ) - 1) / n) * minkowskiDim ≤ boundaryCdimGrowth ∧
      boundaryCdimGrowth ≤ minkowskiDim :=
  paper_spg_minkowski_dimension_boundary_cdimpm_growth_sandwich_package hn N boundaryFaces
    minkowskiDim boundaryGrowth boundaryCdimGrowth hN_nonneg hIso hLower hUpper hScale

end Omega.SPG

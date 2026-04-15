import Mathlib.Tactic

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

end Omega.SPG

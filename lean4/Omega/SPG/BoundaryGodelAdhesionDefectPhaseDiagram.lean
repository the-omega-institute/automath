import Mathlib.Tactic
import Omega.SPG.BulkBoundaryGodelDimensionSandwich
import Omega.SPG.GodelDoublelogMinkowski

namespace Omega.SPG

/-- Paper label: `thm:conclusion-boundary-godel-adhesion-defect-phase-diagram`.
If the boundary exponent is the max of the outer-layer contribution and the adhesion-defect
contribution, the outer-layer term reads `d_G(A) - 1`, and the bulk/boundary sandwich puts the
boundary exponent strictly above `d_G(A) - 1` in the subfull regime, then the adhesion term is
forced to dominate. -/
theorem paper_conclusion_boundary_godel_adhesion_defect_phase_diagram
    {n : ℕ} (hn : 1 ≤ n)
    (bulkGodelDim boundaryGodelDim boundaryGrowth outerLayerDim adhesionDefectDim : ℝ)
    (hOuterLayer : outerLayerDim = bulkGodelDim - 1)
    (hBoundaryMax : boundaryGodelDim = max outerLayerDim adhesionDefectDim)
    (hScale : boundaryGodelDim = boundaryGrowth)
    (hLower : (((n : ℝ) - 1) / n) * bulkGodelDim ≤ boundaryGrowth)
    (hSubfull : bulkGodelDim < n) :
    boundaryGodelDim = max (bulkGodelDim - 1) adhesionDefectDim ∧
      bulkGodelDim - 1 < (((n : ℝ) - 1) / n) * bulkGodelDim ∧
      boundaryGodelDim = adhesionDefectDim := by
  have hPhase : boundaryGodelDim = max (bulkGodelDim - 1) adhesionDefectDim := by
    simpa [hOuterLayer] using hBoundaryMax
  have hSandwichLower : (((n : ℝ) - 1) / n) * bulkGodelDim ≤ boundaryGodelDim := by
    simpa [hScale] using hLower
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := by
    positivity
  have hrewrite :
      bulkGodelDim - bulkGodelDim / (n : ℝ) = (((n : ℝ) - 1) / n) * bulkGodelDim := by
    field_simp [hn_ne]
  have hOuterLt :
      bulkGodelDim - 1 < (((n : ℝ) - 1) / n) * bulkGodelDim := by
    have hdiv : bulkGodelDim / (n : ℝ) < 1 := by
      have hdiv' : bulkGodelDim < 1 * (n : ℝ) := by simpa using hSubfull
      have hquot := div_lt_div_of_pos_right hdiv' hn_pos
      simpa [hn_ne] using hquot
    calc
      bulkGodelDim - 1 < bulkGodelDim - bulkGodelDim / (n : ℝ) := by linarith
      _ = (((n : ℝ) - 1) / n) * bulkGodelDim := hrewrite
  have hOuterLtBoundary : bulkGodelDim - 1 < boundaryGodelDim :=
    lt_of_lt_of_le hOuterLt hSandwichLower
  have hAdhesionNotLe : ¬ adhesionDefectDim ≤ bulkGodelDim - 1 := by
    intro hle
    have hEq : boundaryGodelDim = bulkGodelDim - 1 := by
      rw [hPhase, max_eq_left hle]
    linarith
  have hAdhesionDominates : boundaryGodelDim = adhesionDefectDim := by
    rw [hPhase, max_eq_right (le_of_not_ge hAdhesionNotLe)]
  exact ⟨hPhase, hOuterLt, hAdhesionDominates⟩

end Omega.SPG

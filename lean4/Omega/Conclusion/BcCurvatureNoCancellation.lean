import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A finite Beck--Chevalley curvature tower with layer-localized nonnegative curvature terms. -/
structure conclusion_bc_curvature_no_cancellation_CurvatureTower (k : ℕ) where
  totalDefect : ℝ
  layerCurvature : Fin (k + 1) → ℝ
  conclusion_bc_curvature_no_cancellation_layerCurvature_nonneg :
    ∀ i : Fin (k + 1), 0 ≤ layerCurvature i
  conclusion_bc_curvature_no_cancellation_totalDefect_eq_sum :
    totalDefect = ∑ i : Fin (k + 1), layerCurvature i

/-- Paper label: `thm:conclusion-bc-curvature-no-cancellation`.
For a finite tower whose total Beck--Chevalley defect is the sum of nonnegative localized layer
curvatures, the total defect vanishes exactly when every layer curvature vanishes. -/
theorem paper_conclusion_bc_curvature_no_cancellation {k : ℕ}
    (D : conclusion_bc_curvature_no_cancellation_CurvatureTower k) :
    D.totalDefect = 0 ↔ ∀ i : Fin (k + 1), D.layerCurvature i = 0 := by
  rw [D.conclusion_bc_curvature_no_cancellation_totalDefect_eq_sum]
  simpa using
    (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i : Fin (k + 1) => D.layerCurvature i)
      (fun i _ => D.conclusion_bc_curvature_no_cancellation_layerCurvature_nonneg i))

end Omega.Conclusion

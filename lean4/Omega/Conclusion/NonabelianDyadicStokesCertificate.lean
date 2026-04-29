import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate data for a dyadic nonabelian Stokes grid.  The finite cell type is the
dyadic grid, `h` is the mesh, `C` is the local Stokes constant, and `localError` records the
cellwise transported Stokes error. -/
structure conclusion_nonabelian_dyadic_stokes_certificate_Data where
  Cell : Type
  cellFintype : Fintype Cell
  h : ℝ
  C : ℝ
  localError : Cell → ℝ
  globalError : ℝ
  h_pos : 0 < h
  globalError_eq_sum : globalError = ∑ cell, localError cell
  localError_bound : ∀ cell, localError cell ≤ C * h ^ 3
  grid_cardinality : (Fintype.card Cell : ℝ) = h⁻¹ ^ 2

namespace conclusion_nonabelian_dyadic_stokes_certificate_Data

/-- The recursive dyadic Stokes certificate gives an `O(h)` global error after summing
`O(h^3)` local errors over `h^{-2}` cells. -/
def recursive_stokes_error_bound
    (D : conclusion_nonabelian_dyadic_stokes_certificate_Data) : Prop :=
  D.globalError ≤ D.C * D.h

end conclusion_nonabelian_dyadic_stokes_certificate_Data

open conclusion_nonabelian_dyadic_stokes_certificate_Data

/-- Paper label: `cor:conclusion-nonabelian-dyadic-stokes-certificate`. -/
theorem paper_conclusion_nonabelian_dyadic_stokes_certificate
    (D : conclusion_nonabelian_dyadic_stokes_certificate_Data) :
    D.recursive_stokes_error_bound := by
  letI := D.cellFintype
  have hh_ne : D.h ≠ 0 := ne_of_gt D.h_pos
  calc
    D.globalError = ∑ cell : D.Cell, D.localError cell := D.globalError_eq_sum
    _ ≤ ∑ _cell : D.Cell, D.C * D.h ^ 3 := by
      exact Finset.sum_le_sum fun cell _ => D.localError_bound cell
    _ = (Fintype.card D.Cell : ℝ) * (D.C * D.h ^ 3) := by
      simp
    _ = D.h⁻¹ ^ 2 * (D.C * D.h ^ 3) := by
      rw [D.grid_cardinality]
    _ = D.C * D.h := by
      field_simp [hh_ne]

end Omega.Conclusion

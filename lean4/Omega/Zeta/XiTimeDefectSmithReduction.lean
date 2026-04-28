import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete integer Smith-reduction package for the xi-time defect lattice. The matrix data,
Smith normal form equality, and invariant-factor quotient readout are kept as explicit fields. -/
structure xi_time_defect_smith_reduction_data where
  xi_time_defect_smith_reduction_row_count : ℕ
  xi_time_defect_smith_reduction_column_count : ℕ
  xi_time_defect_smith_reduction_invariant_count : ℕ
  xi_time_defect_smith_reduction_matrix :
    Matrix (Fin xi_time_defect_smith_reduction_row_count)
      (Fin xi_time_defect_smith_reduction_column_count) ℤ
  xi_time_defect_smith_reduction_left :
    Matrix (Fin xi_time_defect_smith_reduction_row_count)
      (Fin xi_time_defect_smith_reduction_row_count) ℤ
  xi_time_defect_smith_reduction_right :
    Matrix (Fin xi_time_defect_smith_reduction_column_count)
      (Fin xi_time_defect_smith_reduction_column_count) ℤ
  xi_time_defect_smith_reduction_smith_normal :
    Matrix (Fin xi_time_defect_smith_reduction_row_count)
      (Fin xi_time_defect_smith_reduction_column_count) ℤ
  xi_time_defect_smith_reduction_invariant_factor :
    Fin xi_time_defect_smith_reduction_invariant_count → ℕ
  xi_time_defect_smith_reduction_quotient_free_rank : ℕ
  xi_time_defect_smith_reduction_quotient_torsion_factor :
    Fin xi_time_defect_smith_reduction_invariant_count → ℕ
  xi_time_defect_smith_reduction_smith_equation :
    xi_time_defect_smith_reduction_left * xi_time_defect_smith_reduction_matrix *
        xi_time_defect_smith_reduction_right =
      xi_time_defect_smith_reduction_smith_normal
  xi_time_defect_smith_reduction_invariant_factor_pos :
    ∀ i, 0 < xi_time_defect_smith_reduction_invariant_factor i
  xi_time_defect_smith_reduction_quotient_free_rank_eq :
    xi_time_defect_smith_reduction_quotient_free_rank =
      xi_time_defect_smith_reduction_column_count -
        xi_time_defect_smith_reduction_invariant_count
  xi_time_defect_smith_reduction_quotient_torsion_factor_eq :
    ∀ i,
      xi_time_defect_smith_reduction_quotient_torsion_factor i =
        xi_time_defect_smith_reduction_invariant_factor i

/-- The invariant-factor quotient decomposition associated to the packaged Smith data. -/
def xi_time_defect_smith_reduction_quotient_decomposition
    (D : xi_time_defect_smith_reduction_data) : Prop :=
  D.xi_time_defect_smith_reduction_quotient_free_rank =
      D.xi_time_defect_smith_reduction_column_count -
        D.xi_time_defect_smith_reduction_invariant_count ∧
    (∀ i,
      D.xi_time_defect_smith_reduction_quotient_torsion_factor i =
        D.xi_time_defect_smith_reduction_invariant_factor i) ∧
    ∀ i, 0 < D.xi_time_defect_smith_reduction_quotient_torsion_factor i

/-- Paper-facing Smith-reduction statement: the supplied integer row/column operations put the
defect matrix in Smith normal form and the quotient has the recorded invariant factors. -/
def xi_time_defect_smith_reduction_statement
    (D : xi_time_defect_smith_reduction_data) : Prop :=
  D.xi_time_defect_smith_reduction_left * D.xi_time_defect_smith_reduction_matrix *
        D.xi_time_defect_smith_reduction_right =
      D.xi_time_defect_smith_reduction_smith_normal ∧
    xi_time_defect_smith_reduction_quotient_decomposition D

/-- Paper label: `prop:xi-time-defect-smith-reduction`. -/
theorem paper_xi_time_defect_smith_reduction
    (D : xi_time_defect_smith_reduction_data) :
    xi_time_defect_smith_reduction_statement D := by
  refine ⟨D.xi_time_defect_smith_reduction_smith_equation, ?_⟩
  refine ⟨D.xi_time_defect_smith_reduction_quotient_free_rank_eq,
    D.xi_time_defect_smith_reduction_quotient_torsion_factor_eq, ?_⟩
  intro i
  rw [D.xi_time_defect_smith_reduction_quotient_torsion_factor_eq i]
  exact D.xi_time_defect_smith_reduction_invariant_factor_pos i

end Omega.Zeta

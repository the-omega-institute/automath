import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete `O(1)` comparison on the logarithmic range `m ≥ 2`. -/
def xi_bulk_boundary_double_scaling_holography_bounded_error (F G : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → |F m - G m| ≤ C

/-- Concrete scaling data for the bulk-boundary double-scaling statement. -/
structure xi_bulk_boundary_double_scaling_holography_data where
  kappa : ℝ
  bulkEntropy : ℕ → ℝ
  boundaryEntropy : ℕ → ℝ
  determinant_scaling_covariance :
    xi_bulk_boundary_double_scaling_holography_bounded_error bulkEntropy
      (fun m => kappa ^ (2 : ℕ) * Real.log (m : ℝ))
  boundary_entropy_linear_law :
    ∀ m : ℕ, 2 ≤ m → boundaryEntropy m = kappa * Real.log (m : ℝ)

/-- The bulk entropy has quadratic logarithmic scaling. -/
def xi_bulk_boundary_double_scaling_holography_data.bulk_quadratic_scaling
    (D : xi_bulk_boundary_double_scaling_holography_data) : Prop :=
  xi_bulk_boundary_double_scaling_holography_bounded_error D.bulkEntropy
    (fun m => D.kappa ^ (2 : ℕ) * Real.log (m : ℝ))

/-- The bulk entropy is quadratically comparable to the boundary entropy. -/
def xi_bulk_boundary_double_scaling_holography_data.bulk_boundary_scaling
    (D : xi_bulk_boundary_double_scaling_holography_data) : Prop :=
  xi_bulk_boundary_double_scaling_holography_bounded_error D.bulkEntropy
    (fun m => D.boundaryEntropy m ^ (2 : ℕ) / Real.log (m : ℝ))

lemma xi_bulk_boundary_double_scaling_holography_boundary_quadratic_identity
    (D : xi_bulk_boundary_double_scaling_holography_data) {m : ℕ} (hm : 2 ≤ m) :
    D.boundaryEntropy m ^ (2 : ℕ) / Real.log (m : ℝ) =
      D.kappa ^ (2 : ℕ) * Real.log (m : ℝ) := by
  have hlog_pos : 0 < Real.log (m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hm)
  rw [D.boundary_entropy_linear_law m hm]
  field_simp [ne_of_gt hlog_pos]

/-- Paper label: `cor:xi-bulk-boundary-double-scaling-holography`. -/
theorem paper_xi_bulk_boundary_double_scaling_holography
    (D : xi_bulk_boundary_double_scaling_holography_data) :
    D.bulk_quadratic_scaling ∧ D.bulk_boundary_scaling := by
  refine ⟨D.determinant_scaling_covariance, ?_⟩
  rcases D.determinant_scaling_covariance with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro m hm
  have hquad :
      D.boundaryEntropy m ^ (2 : ℕ) / Real.log (m : ℝ) =
        D.kappa ^ (2 : ℕ) * Real.log (m : ℝ) :=
    xi_bulk_boundary_double_scaling_holography_boundary_quadratic_identity D hm
  simpa [hquad] using hC m hm

end Omega.Zeta

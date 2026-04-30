import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete capacity/residual interface for the Mellin identity.  The scalar fields stand for
the two Mellin integrals, while the functional fields record the derivative and boundary
certificates used by the integration-by-parts step. -/
structure xi_time_part9m3_capacity_defect_residual_coherence_mellin_data where
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_m : ℕ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_q : ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_moment : ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_mellin : ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_mellin : ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_defect : ℝ → ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_coherence : ℝ → ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_derivative : ℝ → ℝ
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_q_gt_one :
    1 < xi_time_part9m3_capacity_defect_residual_coherence_mellin_q
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_q_gt_two :
    2 < xi_time_part9m3_capacity_defect_residual_coherence_mellin_q
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_moment_interface :
    xi_time_part9m3_capacity_defect_residual_coherence_mellin_moment =
      xi_time_part9m3_capacity_defect_residual_coherence_mellin_q *
        (xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 1) *
          xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_mellin
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_ae_derivative_identity :
    ∀ T : ℝ, 0 < T →
      xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_defect T =
        -(((2 : ℝ) ^ xi_time_part9m3_capacity_defect_residual_coherence_mellin_m) / 2) *
          xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_derivative T
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_compact_support_boundary :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ T : ℝ, B ≤ T →
        xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_coherence T = 0
  xi_time_part9m3_capacity_defect_residual_coherence_mellin_integration_by_parts :
    xi_time_part9m3_capacity_defect_residual_coherence_mellin_q *
        (xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 1) *
          xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_mellin =
      xi_time_part9m3_capacity_defect_residual_coherence_mellin_q *
        (xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 1) *
          (xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 2) *
            (((2 : ℝ) ^
              xi_time_part9m3_capacity_defect_residual_coherence_mellin_m) / 2) *
              xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_mellin

/-- The first Mellin moment identity and its residual-coherence form. -/
def xi_time_part9m3_capacity_defect_residual_coherence_mellin_statement
    (D : xi_time_part9m3_capacity_defect_residual_coherence_mellin_data) : Prop :=
  D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_moment =
      D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_q *
        (D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 1) *
          D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_mellin ∧
    D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_moment =
      D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_q *
        (D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 1) *
          (D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_q - 2) *
            (((2 : ℝ) ^
              D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_m) / 2) *
              D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_mellin ∧
    (∀ T : ℝ, 0 < T →
      D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_defect T =
        -(((2 : ℝ) ^ D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_m) / 2) *
          D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_derivative T) ∧
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ T : ℝ, B ≤ T →
        D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_residual_coherence T = 0)

/-- Paper label: `thm:xi-time-part9m3-capacity-defect-residual-coherence-mellin`. -/
theorem paper_xi_time_part9m3_capacity_defect_residual_coherence_mellin
    (D : xi_time_part9m3_capacity_defect_residual_coherence_mellin_data) :
    xi_time_part9m3_capacity_defect_residual_coherence_mellin_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_moment_interface
  · exact
      D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_capacity_moment_interface.trans
        D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_integration_by_parts
  · exact D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_ae_derivative_identity
  · exact D.xi_time_part9m3_capacity_defect_residual_coherence_mellin_compact_support_boundary

end Omega.Zeta

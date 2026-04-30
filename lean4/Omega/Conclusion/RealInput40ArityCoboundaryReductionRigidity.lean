import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed
import Omega.SyncKernelWeighted.RealInput40ArityChargeSimilarityReduction
import Omega.SyncKernelWeighted.RealInput40ZetaUvRecurrence

namespace Omega.Conclusion

open Omega.SyncKernelWeighted

/-- Paper-facing conclusion package for the real-input-40 arity-charge reduction: the existing
coboundary certificate gives the normalized charge package, the one-state reduction preserves
determinant and trace, the audited determinant factorization is available, and the primitive
Möbius recovery holds for every weighted trace channel. -/
def conclusion_realinput40_arity_coboundary_reduction_rigidity_statement
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) : Prop :=
  D.coboundaryNormalization ∧
    D.edgeAuditWithPotential ∧
    D.primitiveCycleDensityBound ∧
    real_input_40_arity_charge_similarity_reduction_statement D ∧
    Matrix.det prop_real_input_40_arity_charge_similarity_reduction_charge_matrix =
      Matrix.det prop_real_input_40_arity_charge_similarity_reduction_base_matrix ∧
    Matrix.trace prop_real_input_40_arity_charge_similarity_reduction_charge_matrix =
      Matrix.trace prop_real_input_40_arity_charge_similarity_reduction_base_matrix ∧
    (∀ z q : ℚ,
      real_input_40_arity_charge_det_closed_det z q =
        (1 + z) * (1 - q * z ^ 2) * real_input_40_arity_charge_det_closed_Q7 z q) ∧
    (∀ Λ q : ℚ,
      real_input_40_arity_charge_det_closed_charpoly Λ q =
        Λ ^ 10 * (Λ + 1) * (Λ ^ 2 - q) * real_input_40_arity_charge_det_closed_P7 Λ q) ∧
    (∀ u v : ℝ, real_input_40_zeta_uv_recurrence_primitive_recoverable u v)

/-- Paper label: `thm:conclusion-realinput40-arity-coboundary-reduction-rigidity`. -/
theorem paper_conclusion_realinput40_arity_coboundary_reduction_rigidity
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) :
    conclusion_realinput40_arity_coboundary_reduction_rigidity_statement D := by
  rcases paper_real_input_40_arity_charge_coboundary D with ⟨hNorm, hAudit, hBound⟩
  have hReduction := paper_real_input_40_arity_charge_similarity_reduction D
  rcases hReduction with ⟨_, _, _, _, _, hDet, hTrace⟩
  rcases paper_real_input_40_arity_charge_det_closed with ⟨hDetZ, hCharpoly, _, _⟩
  refine ⟨hNorm, hAudit, hBound, paper_real_input_40_arity_charge_similarity_reduction D,
    hDet, hTrace, hDetZ, hCharpoly, ?_⟩
  intro u v
  exact (paper_real_input_40_zeta_uv_recurrence u v).2

end Omega.Conclusion

import Mathlib.Tactic
import Omega.Conclusion.ToeplitzNegativeGeometryStrictificationOrthogonalSplit
import Omega.Zeta.FiniteDefectCompleteReconstruction

namespace Omega.Conclusion

open Omega.Zeta

/-- A macroscopic Toeplitz audit scale has at least near-quadratic size compared to the intrinsic
finite-defect rank. -/
def conclusion_finite_defect_rank_vs_macroscopic_toeplitz_audit_scale_splitting_audit_scale
    (κ auditScale : ℕ) : Prop :=
  2 * κ ≤ auditScale ^ 2

/-- Paper label: `thm:conclusion-finite-defect-rank-vs-macroscopic-toeplitz-audit-scale-splitting`.
The finite-defect scan package supplies the readable defect count together with the moment and
sample reconstructions and the short-prefix obstruction, while the Toeplitz negative-geometry
wrapper provides the concrete negative Hankel witness block. The macroscopic audit cost is recorded
by the explicit near-quadratic scale inequality. -/
theorem paper_conclusion_finite_defect_rank_vs_macroscopic_toeplitz_audit_scale_splitting
    {β : Type*} (audit : (ℂ → ℂ) → β)
    (hAudit : toeplitzAuditFactorsThroughKernel audit)
    (κ auditScale : ℕ) (D : FiniteDefectCompleteReconstructionData κ)
    (σ v : Fin κ → ℝ) (C : ℂ → ℂ) (η : ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0)
    (hauditScale :
      conclusion_finite_defect_rank_vs_macroscopic_toeplitz_audit_scale_splitting_audit_scale
        κ auditScale) :
    D.kappaReadable ∧
      D.reconstructionFromMomentSegment ∧
      D.reconstructionFrom4KappaSamples ∧
      xi_scan_minimal_complete_2kappa_short_prefix_nonuniqueness κ ∧
      toeplitzNegativeWitness σ v < 0 ∧
      conclusion_finite_defect_rank_vs_macroscopic_toeplitz_audit_scale_splitting_audit_scale
        κ auditScale := by
  rcases paper_xi_scan_minimal_complete_2kappa κ D with
    ⟨hkappa, hMoment, hSamples, _, hshort⟩
  rcases
      paper_conclusion_toeplitz_negative_geometry_strictification_orthogonal_split
        audit hAudit σ v C η hnonzero with
    ⟨_, _, _, hneg, _, _⟩
  exact ⟨hkappa, hMoment, hSamples, hshort, hneg, hauditScale⟩

end Omega.Conclusion

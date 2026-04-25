import Mathlib.Tactic
import Omega.Zeta.HankelRankMinimalLinearRealization
import Omega.Zeta.XiHankelLiftingBranchCountAffineSolutionSpace
import Omega.Zeta.XiHankelOfflineModularAuditThreshold
import Omega.Zeta.XiHankelSigminLowerboundVandermondeSeparation
import Omega.Zeta.XiHankelSpikeSingularSpectrumSeparation

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the Prony/Hankel root-stability certificate. The spectral separation and
smallest-singular-value packages control invertibility, the maximal-minor syndrome package gives
the companion recurrence, the affine lifting theorem records the solution fiber, and the modular
audit supplies the recursive posterior certificate. -/
structure xi_hankel_prony_root_stability_recursive_certificate_data where
  spikeData : XiHankelSpikeSingularSpectrumData
  sigminData : XiHankelSigminLowerboundData
  syndromeData : HankelMaximalMinorSyndromeData ℚ
  auditData : XiHankelOfflineModularAuditData
  p : ℕ
  k : ℕ
  d : ℕ
  C : ℝ
  ε : ℝ
  hC_pos : 0 < C
  hε_nonneg : 0 ≤ ε
  hsigmaMin_pos : 0 < sigminData.sigmaMin
  hneumann : ε ≤ sigminData.sigmaMin / (2 * C)

/-- Certified root radius produced by the Neumann/Bauer--Fike bookkeeping package. -/
def xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius
    (D : xi_hankel_prony_root_stability_recursive_certificate_data) : ℝ :=
  D.C * D.ε / D.sigminData.sigmaMin

/-- Paper-facing recursive certificate: singular-spectrum separation, the Vandermonde/sigmin lower
bound, the unique Prony recurrence, the affine lifting count, the modular posterior certificate,
and the explicit root-radius bound all hold simultaneously. -/
def xi_hankel_prony_root_stability_recursive_certificate_statement
    (D : xi_hankel_prony_root_stability_recursive_certificate_data) : Prop :=
  D.spikeData.singularSpectrumSeparated ∧
    (D.sigminData.determinantLowerBound ∧
      D.sigminData.operatorNormUpperBound ∧ D.sigminData.sigmaMinLowerBound) ∧
    (D.syndromeData.kernelLineGeneratedBySyndrome ∧
      D.syndromeData.monicRecurrenceUnique ∧ D.syndromeData.shiftCompanionAnnihilated) ∧
    xi_hankel_lifting_branch_count_affine_solution_space_solution_count D.p D.k D.d =
      D.p ^ (D.d * xi_hankel_lifting_branch_count_affine_solution_space_Hp D.p D.k) ∧
    D.auditData.auditThresholdCertifiesUniqueSolution ∧
    0 ≤ xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius D ∧
      xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius D ≤ 1 / 2

/-- Paper label: `thm:xi-hankel-prony-root-stability-recursive-certificate`. -/
theorem paper_xi_hankel_prony_root_stability_recursive_certificate
    (D : xi_hankel_prony_root_stability_recursive_certificate_data) :
    xi_hankel_prony_root_stability_recursive_certificate_statement D := by
  have hSpike := paper_xi_hankel_spike_singular_spectrum_separation D.spikeData
  have hSig := paper_xi_hankel_sigmin_lowerbound_vandermonde_separation D.sigminData
  have hRec := paper_xi_hankel_rank_minimal_linear_realization D.syndromeData
  have hLift := paper_xi_hankel_lifting_branch_count_affine_solution_space D.p D.k D.d
  have hAudit := paper_xi_hankel_offline_modular_audit_threshold D.auditData
  have hroot_nonneg :
      0 ≤ xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius D := by
    unfold xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius
    exact div_nonneg (mul_nonneg (le_of_lt D.hC_pos) D.hε_nonneg) (le_of_lt D.hsigmaMin_pos)
  have hroot_le_half :
      xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius D ≤ 1 / 2 := by
    have hC_ne : D.C ≠ 0 := ne_of_gt D.hC_pos
    have hsigma_ne : D.sigminData.sigmaMin ≠ 0 := ne_of_gt D.hsigmaMin_pos
    have hscaled :
        D.C * D.ε ≤ D.sigminData.sigmaMin / 2 := by
      have hmul := mul_le_mul_of_nonneg_left D.hneumann (le_of_lt D.hC_pos)
      simpa [div_eq_mul_inv, hC_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
    unfold xi_hankel_prony_root_stability_recursive_certificate_certified_root_radius
    calc
      D.C * D.ε / D.sigminData.sigmaMin ≤
          (D.sigminData.sigmaMin / 2) / D.sigminData.sigmaMin := by
            exact div_le_div_of_nonneg_right hscaled (le_of_lt D.hsigmaMin_pos)
      _ = 1 / 2 := by
            field_simp [hsigma_ne]
  exact ⟨hSpike, hSig, hRec, hLift, hAudit, hroot_nonneg, hroot_le_half⟩

end

end Omega.Zeta

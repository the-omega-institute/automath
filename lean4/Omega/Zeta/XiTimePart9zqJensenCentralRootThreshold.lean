import Mathlib.Tactic
import Omega.Zeta.XiJensenDefectNoisyThreepointCertificate

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete data for the Jensen central-root continuation threshold.  The weight `centralWeight`
is the certified noisy second-difference margin after the `4ε` audit loss. -/
structure xi_time_part9zq_jensen_central_root_threshold_Data where
  certificate : xi_jensen_defect_noisy_threepoint_certificate_Data
  centralWeight : ℝ
  centralWeight_eq :
    centralWeight = certificate.noisySecondDifference - 4 * certificate.ε
  exactSecondDifference_eq_hat :
    certificate.exactSecondDifference = certificate.hatSecondDifference
  centralWeight_lower_bound : certificate.h - 4 * certificate.ε ≤ centralWeight
  continuation_budget : 16 * certificate.ε ≤ 3 * certificate.h
  sharp_budget : 32 * certificate.ε ≤ 7 * certificate.h
  scale_pos : 0 < certificate.h

namespace xi_time_part9zq_jensen_central_root_threshold_Data

/-- The continuation trigger clears the `h/4` Jensen margin. -/
def continuationThreshold
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) : Prop :=
  D.certificate.h / 4 ≤ D.centralWeight

/-- The finite three-point certificate: error audit, window atom, and multiplicity lower bound. -/
def finiteThreePointCertificate
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) : Prop :=
  D.certificate.noisySecondDifferenceErrorBound ∧
    (∃ i, 0 < D.certificate.hatKernel (D.certificate.location i)) ∧
    D.centralWeight ≤
      D.certificate.h * ∑ i, (D.certificate.multiplicity i : ℝ)

/-- The sharper `h/8` continuation margin recorded by the stronger budget. -/
def sharpContinuationConstant
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) : Prop :=
  D.certificate.h / 8 ≤ D.centralWeight

lemma continuationThreshold_intro
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) :
    D.continuationThreshold := by
  unfold continuationThreshold
  linarith [D.centralWeight_lower_bound, D.continuation_budget]

lemma sharpContinuationConstant_intro
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) :
    D.sharpContinuationConstant := by
  unfold sharpContinuationConstant
  linarith [D.centralWeight_lower_bound, D.sharp_budget]

lemma finiteThreePointCertificate_intro
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) :
    D.finiteThreePointCertificate := by
  have hpackage := paper_xi_jensen_defect_noisy_threepoint_certificate D.certificate
  rcases hpackage with ⟨herror, hwindow, hmultiplicity⟩
  have hcontinuation : D.continuationThreshold := D.continuationThreshold_intro
  have hthreshold : 4 * D.certificate.ε < D.certificate.noisySecondDifference := by
    unfold continuationThreshold at hcontinuation
    linarith [D.centralWeight_eq, hcontinuation, D.scale_pos]
  have hwindow_atom :
      ∃ i, 0 < D.certificate.hatKernel (D.certificate.location i) :=
    hwindow D.exactSecondDifference_eq_hat hthreshold
  have hmultiplicity_bound :
      D.centralWeight ≤
        D.certificate.h * ∑ i, (D.certificate.multiplicity i : ℝ) := by
    rw [D.centralWeight_eq]
    exact hmultiplicity D.exactSecondDifference_eq_hat hthreshold
  exact ⟨herror, hwindow_atom, hmultiplicity_bound⟩

end xi_time_part9zq_jensen_central_root_threshold_Data

/-- Paper label: `thm:xi-time-part9zq-jensen-central-root-threshold`. -/
theorem paper_xi_time_part9zq_jensen_central_root_threshold
    (D : xi_time_part9zq_jensen_central_root_threshold_Data) :
    D.continuationThreshold ∧ D.finiteThreePointCertificate ∧
      D.sharpContinuationConstant := by
  exact ⟨D.continuationThreshold_intro, D.finiteThreePointCertificate_intro,
    D.sharpContinuationConstant_intro⟩

end Omega.Zeta

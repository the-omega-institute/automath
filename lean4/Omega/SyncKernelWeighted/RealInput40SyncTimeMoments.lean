import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40Essential20
import Omega.SyncKernelWeighted.RealInput40EssentialReduction
import Omega.SyncKernelWeighted.RealInput40FibTensorRHSharpClosure
import Omega.SyncKernelWeighted.RealInput40ResetRegenerationConstants
import Omega.SyncKernelWeighted.RealInput40ResetRegenerationCovBound
import Omega.SyncKernelWeighted.RealInput40ResetWord
import Omega.SyncKernelWeighted.RealInput40ZeroTempGroundSftParryClosedForm

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete wrapper for the audited real-input-40 synchronization-time package. The imported
modules supply the reset word, the essential-20 reduction, the reset-regeneration constants,
the covariance decay audit, and the RH-sharp spectral closure; the scalar fields record the chosen
closed forms for the mean, variance, and transient spectral radius. -/
structure RealInput40SyncTimeMomentsData where
  reduction : RealInput40EssentialReductionData
  covariance : RealInput40ResetRegenerationCovBoundData
  rhsharp : FibTensorRhsharpClosureData
  parry : RealInput40ZeroTempGroundSftParryClosedFormData
  meanSyncTime : ℝ
  varianceSyncTime : ℝ
  transientSpectralRadius : ℝ
  mean_closed_form :
    meanSyncTime = realInput40ResetRegenerationCertificate.kacReturnTime
  variance_closed_form :
    varianceSyncTime = realInput40ResetRegenerationCertificate.typicalNonResetWait
  theta_is_golden_ratio : parry.θ = Real.goldenRatio
  spectralRadius_eq_theta_inv : transientSpectralRadius = parry.θ⁻¹

namespace RealInput40SyncTimeMomentsData

/-- Closed-form mean/variance package together with the reset, essential-core, and covariance
audits needed for the synchronization-time moment calculation. -/
def closedFormMoments (D : RealInput40SyncTimeMomentsData) : Prop :=
  RealInput40ResetWordStatement ∧
    realInput40Vertices.card = 40 ∧
    realInput40EssentialCore.card = 20 ∧
    realInput40TransientShell.card = 20 ∧
    RealInput40EssentialReduction D.reduction ∧
    realInput40ResetSectorProbabilityClosedForm ∧
    realInput40KacReturnTimeClosedForm ∧
    realInput40TypicalWaitTimeClosedForm ∧
    D.covariance.pointwiseCovarianceBound ∧
    D.covariance.exponentialCovarianceBound ∧
    D.meanSyncTime = realInput40ResetRegenerationCertificate.kacReturnTime ∧
    D.varianceSyncTime = realInput40ResetRegenerationCertificate.typicalNonResetWait

/-- Closed-form transient spectral radius together with the audited Parry and RH-sharp packages. -/
def spectralRadiusClosedForm (D : RealInput40SyncTimeMomentsData) : Prop :=
  D.parry.rightPerronVectorClosedForm ∧
    D.parry.leftPerronVectorClosedForm ∧
    D.parry.parryTransitionClosedForm ∧
    D.parry.stationaryDistributionClosedForm ∧
    D.rhsharp.spectralRadiusFormula ∧
    D.rhsharp.rhsharpBound ∧
    D.rhsharp.tracePrimitiveClosedForm ∧
    D.transientSpectralRadius = (Real.goldenRatio : ℝ)⁻¹

end RealInput40SyncTimeMomentsData

open RealInput40SyncTimeMomentsData

/-- Paper label: `prop:real-input-40-sync-time-moments`. The already audited reset word,
essential-20 reduction, reset-regeneration constants, covariance bound, and RH-sharp closure
assemble into a closed-form synchronization-time package; the transient spectral radius is the
inverse golden ratio. -/
theorem paper_real_input_40_sync_time_moments (D : RealInput40SyncTimeMomentsData) :
    D.closedFormMoments ∧ D.spectralRadiusClosedForm := by
  have hEssential := paper_real_input_40_essential_20
  have hReduction : RealInput40EssentialReduction D.reduction :=
    paper_real_input_40_essential_reduction D.reduction
  have hConstants := paper_real_input_40_reset_regeneration_constants
  have hCovariance :
      D.covariance.pointwiseCovarianceBound ∧ D.covariance.exponentialCovarianceBound :=
    paper_real_input_40_reset_regeneration_cov_bound D.covariance
  have hParry :
      D.parry.rightPerronVectorClosedForm ∧ D.parry.leftPerronVectorClosedForm ∧
        D.parry.parryTransitionClosedForm ∧ D.parry.stationaryDistributionClosedForm :=
    paper_killo_real_input_40_zero_temp_ground_sft_parry_closed_form D.parry
  have hRh :
      D.rhsharp.spectralRadiusFormula ∧ D.rhsharp.rhsharpBound ∧
        D.rhsharp.tracePrimitiveClosedForm :=
    paper_fib_tensor_rhsharp_closure D.rhsharp
  refine ⟨?_, ?_⟩
  · rcases hEssential with
      ⟨hVertices, _, _, _, _, hCore, hShell, _, _, _, _⟩
    exact ⟨paper_real_input_40_reset_word, hVertices, hCore, hShell, hReduction, hConstants.1,
      hConstants.2.1, hConstants.2.2, hCovariance.1, hCovariance.2, D.mean_closed_form,
      D.variance_closed_form⟩
  · refine ⟨hParry.1, hParry.2.1, hParry.2.2.1, hParry.2.2.2, hRh.1, hRh.2.1, hRh.2.2, ?_⟩
    calc
      D.transientSpectralRadius = D.parry.θ⁻¹ := D.spectralRadius_eq_theta_inv
      _ = (Real.goldenRatio : ℝ)⁻¹ := by rw [D.theta_is_golden_ratio]

end

end Omega.SyncKernelWeighted

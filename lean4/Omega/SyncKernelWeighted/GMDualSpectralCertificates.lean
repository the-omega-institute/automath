import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF
import Omega.SyncKernelWeighted.GMResidualOpnormGramEquivalence
import Omega.SyncKernelWeighted.GMTrace3SpectralNormExtremal

namespace Omega.SyncKernelWeighted

/-- Concrete dual-certificate package tying together the continuous trace-`3` spectral bound and
the finite-state additive-energy Perron certificate. -/
structure GMDualSpectralCertificatesData where
  residualData : gm_residual_opnorm_gram_equivalence_data
  traceMultiplicity : ℕ
  traceMultiplicity_ge_two : 2 ≤ traceMultiplicity
  traceSum : ℝ
  traceMoment3 : ℝ
  spectralOffset : ℝ
  spectralDisplacement : ℝ
  traceSum_nonneg : 0 ≤ traceSum
  spectralOffset_nonneg : 0 ≤ spectralOffset
  spectralOffset_le_displacement : spectralOffset ≤ spectralDisplacement

namespace GMDualSpectralCertificatesData

/-- Continuous-side certificate: the residual/opnorm comparison is combined with the trace-`3`
Jensen envelope and cubic characterization from the spectral-norm extremal theorem. -/
def traceResidualCertified (D : GMDualSpectralCertificatesData) : Prop :=
  let x := D.traceSum / (D.traceMultiplicity : ℝ) + D.spectralOffset
  let x' := D.traceSum / (D.traceMultiplicity : ℝ) + D.spectralDisplacement
  let y := (D.traceSum - x) / (D.traceMultiplicity - 1 : ℝ)
  gm_residual_opnorm_gram_equivalence_data.statement D.residualData ∧
    gmTrace3LowerEnvelope D.traceMultiplicity D.traceSum x ≤
      gmTrace3LowerEnvelope D.traceMultiplicity D.traceSum x' ∧
    (gmTrace3LowerEnvelope D.traceMultiplicity D.traceSum x = D.traceMoment3 ↔
      gmTrace3Cubic D.traceMultiplicity D.traceSum D.traceMoment3 x = 0) ∧
    x + (D.traceMultiplicity - 1 : ℝ) * y = D.traceSum ∧
    x ^ 3 + (D.traceMultiplicity - 1 : ℝ) * y ^ 3 =
      gmTrace3LowerEnvelope D.traceMultiplicity D.traceSum x

/-- Discrete-side certificate: the Zeckendorf/sofic additive-energy package reduces to the
finite-state Perron certificate already proven in the real-input appendix. -/
def additiveEnergyCertified (_D : GMDualSpectralCertificatesData) : Prop :=
  Omega.SyncKernelRealInput.gm_sofic_zeck_linear_constraints_pf_statement

end GMDualSpectralCertificatesData

open GMDualSpectralCertificatesData

/-- Paper label: `thm:gm-dual-spectral-certificates`. The continuous trace-`3` residual/opnorm
certificate and the Zeckendorf/sofic finite-state Perron certificate are independent proof
streams, so the dual package is their conjunction. -/
theorem paper_gm_dual_spectral_certificates (D : GMDualSpectralCertificatesData) :
    D.traceResidualCertified ∧ D.additiveEnergyCertified := by
  refine ⟨?_, ?_⟩
  · dsimp [GMDualSpectralCertificatesData.traceResidualCertified]
    refine ⟨paper_gm_residual_opnorm_gram_equivalence D.residualData, ?_⟩
    simpa using
      (paper_gm_trace3_spectral_norm_extremal
        D.traceMultiplicity
        D.traceMultiplicity_ge_two
        (S1 := D.traceSum)
        (S3 := D.traceMoment3)
        (u := D.spectralOffset)
        (v := D.spectralDisplacement)
        D.traceSum_nonneg
        D.spectralOffset_nonneg
        D.spectralOffset_le_displacement)
  · dsimp [GMDualSpectralCertificatesData.additiveEnergyCertified]
    exact Omega.SyncKernelRealInput.paper_gm_sofic_zeck_linear_constraints_pf

end Omega.SyncKernelWeighted

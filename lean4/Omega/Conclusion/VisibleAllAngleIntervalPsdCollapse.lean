import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComputableCertificateTemplate
import Omega.Zeta.ToeplitzPsdCoherenceHorizonThreshold
import Omega.Zeta.XiOracleCollapseToeplitzPsdFiniteTruncation

namespace Omega.Conclusion

open Matrix

/-- Concrete visible-all-angle PSD-collapse data: the Toeplitz probe/horizon package supplies the
bounded-dimension Gram test, the typed-address certificate supplies the interval audit, and the
oracle-collapse package supplies the finite truncation witness that works uniformly over all angle
parameters. -/
structure conclusion_visible_all_angle_interval_psd_collapse_data where
  κ : ℕ
  N : ℕ
  T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  ω : Fin (N + 1) → ℝ
  hω : Function.Injective ω
  reconstruction : Omega.Zeta.FiniteDefectCompleteReconstructionData κ
  intervalAudit :
    Omega.TypedAddressBiaxialCompletion.ComputableCertificateTemplateData
  oracleCollapse : Omega.Zeta.XiOracleCollapseToeplitzPsdData
  oracleBound_le_kappa : oracleCollapse.uniformBound ≤ κ

/-- Statement of the visible-all-angle PSD collapse: the Toeplitz/Gram congruence and
finite-defect recovery data are available, the interval audit compiles to the offline verifier, and
there is a single truncation level `N₀ ≤ 2κ` whose compression witness works uniformly for every
angle parameter. -/
def conclusion_visible_all_angle_interval_psd_collapse_statement
    (D : conclusion_visible_all_angle_interval_psd_collapse_data) : Prop :=
  Omega.Zeta.adamsBinomialProbeKernelMatrix D.N D.T D.ω =
      (((4 : ℝ) ^ D.N)⁻¹) •
        ((Omega.Zeta.adamsBinomialProbeMatrix D.N D.ω)ᴴ * D.T *
          Omega.Zeta.adamsBinomialProbeMatrix D.N D.ω) ∧
    (D.T.PosSemidef ↔
      ((Omega.Zeta.adamsBinomialProbeMatrix D.N D.ω)ᴴ * D.T *
        Omega.Zeta.adamsBinomialProbeMatrix D.N D.ω).PosSemidef) ∧
    D.reconstruction.kappaReadable ∧
    D.reconstruction.reconstructionFrom4KappaSamples ∧
    D.reconstruction.reconstructionFromMomentSegment ∧
    D.reconstruction.strictificationInvariant ∧
    D.intervalAudit.hasIntervalErrorBudget ∧
    D.intervalAudit.compilesToOfflineVerifier ∧
    ∃ N₀ : ℕ, N₀ ≤ 2 * D.κ ∧
      D.oracleCollapse.finiteTruncationEquivalent N₀ ∧
      ∀ ell theta N, ∃ W, D.oracleCollapse.congruenceWitness N₀ ell theta N W

/-- Paper label: `thm:conclusion-visible-all-angle-interval-psd-collapse`. The existing
Toeplitz-to-Gram congruence, the interval-audit reduction, and the finite truncation collapse
assemble into a single witness bounded by `2κ` that works uniformly across all angle parameters. -/
theorem paper_conclusion_visible_all_angle_interval_psd_collapse
    (D : conclusion_visible_all_angle_interval_psd_collapse_data) :
    conclusion_visible_all_angle_interval_psd_collapse_statement D := by
  rcases Omega.Zeta.paper_xi_toeplitz_psd_coherence_horizon_threshold
      D.κ D.N D.T D.ω D.hω D.reconstruction with
    ⟨hKernel, hPSD, hReadable, h4κ, h2κ, hStrict, _hWitness⟩
  have hInterval :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_computable_certificate_template
      D.intervalAudit
  rcases Omega.Zeta.paper_xi_oracle_collapse_toeplitz_psd_finite_truncation D.oracleCollapse with
    ⟨N₀, hN₀, hCollapse, hCongruence⟩
  have hN₀' : N₀ ≤ 2 * D.κ := by
    exact le_trans hN₀ (Nat.mul_le_mul_left 2 D.oracleBound_le_kappa)
  exact ⟨hKernel, hPSD, hReadable, h4κ, h2κ, hStrict, hInterval.2.2.2.1, hInterval.2.2.2.2,
    ⟨N₀, hN₀', hCollapse, hCongruence⟩⟩

end Omega.Conclusion

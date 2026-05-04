import Omega.Conclusion.HardyFiltrationExactProjectionAlgebra
import Omega.Conclusion.HardyChristoffelCompleteFlatness
import Omega.Conclusion.MajorarcDenominatorConstantRamanujanNormalForm
import Omega.Conclusion.FareyLimitKernelFourierDiagonalization
import Omega.Conclusion.FareyLowtemperatureRankoneConstantCollapse
import Omega.Conclusion.FareyHightemperatureFixedbandFlattening
import Omega.Conclusion.ContinuousStrictDropImpliesDiscreteFiniteCertificate
import Omega.Conclusion.DiscreteNearresonanceExtractsContinuousResonantPhase

namespace Omega.Conclusion

open Filter Topology

/-- Concrete inputs for the conclusion rigidity chain.  Each field is an actual parameter or proof
obligation for one of the previously formalized components in the chain. -/
structure conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain_data where
  hardyH : Type
  hardyM : ℕ
  hardyN : ℕ
  hardyPiM : hardyH → hardyH
  hardyPiN : hardyH → hardyH
  hardyRankDiff : ℕ
  hardyMN : ∀ x, hardyPiM (hardyPiN x) = hardyPiN x
  hardyNM : ∀ x, hardyPiN (hardyPiM x) = hardyPiN x
  hardyRank : hardyRankDiff = hardyM - hardyN
  christoffelN : ℕ
  christoffelN_pos : 1 ≤ christoffelN
  christoffelKdiag : ℝ
  christoffelMinNorm : ℝ
  christoffelKdiag_eq : christoffelKdiag = (christoffelN : ℝ)
  christoffelMinNorm_eq : christoffelMinNorm = 1 / christoffelKdiag
  ramanujanData : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data
  fareyData : conclusion_farey_limit_kernel_fourier_diagonalization_data
  lowtemperatureTailBound : ℝ → ℝ
  lowtemperatureDecay :
    ∀ ε > 0, ∃ R > 0, ∀ s, R ≤ s → lowtemperatureTailBound s ≤ ε
  hightemperatureBand : ℕ
  hightemperatureEigenvalueDefect : Fin hightemperatureBand → ℕ → ℝ
  hightemperaturePointwise :
    ∀ n : Fin hightemperatureBand,
      Tendsto (fun tau : ℕ => hightemperatureEigenvalueDefect n tau) atTop (𝓝 0)
  strictDropK : ℝ
  strictDropDiscrete : ℕ → ℝ
  strictDropEps : ℝ
  strictDropEps_pos : 0 < strictDropEps
  strictDropBound : strictDropK ≤ 1 - strictDropEps
  strictDropConvergence :
    ∃ M0, ∀ M ≥ M0, |strictDropDiscrete M - strictDropK| ≤ strictDropEps / 2
  nearresonanceDiscrete : ℕ → ℝ
  nearresonanceContinuous : ℕ → ℝ
  nearresonanceDiscrete_tends :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, |nearresonanceDiscrete j - 1| < ε
  nearresonanceTransfer :
    ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, ∀ j ≥ J, |nearresonanceDiscrete j - nearresonanceContinuous j| < ε

namespace conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain_data

/-- The assembled concrete chain statement. -/
def statement
    (D : conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain_data) : Prop :=
  (∀ x, D.hardyPiM (D.hardyPiN x) = D.hardyPiN x) ∧
    (∀ x, D.hardyPiN (D.hardyPiM x) = D.hardyPiN x) ∧
    D.hardyRankDiff = D.hardyM - D.hardyN ∧
    D.christoffelMinNorm = 1 / (D.christoffelN : ℝ) ∧
    D.christoffelKdiag = (D.christoffelN : ℝ) ∧
    D.ramanujanData.weightedIsometry ∧
    D.ramanujanData.gramRestrictionRamanujanMatrix ∧
    D.fareyData.conclusion_farey_limit_kernel_fourier_diagonalization_statement ∧
    (∀ ε > 0, ∃ τ0 > 0, ∀ τ, 0 < τ → τ ≤ τ0 →
      D.lowtemperatureTailBound (1 / τ) ≤ ε) ∧
    Tendsto
      (fun tau : ℕ =>
        conclusion_farey_hightemperature_fixedband_flattening_band_norm
          D.hightemperatureEigenvalueDefect tau)
      atTop (𝓝 0) ∧
    (∃ M0, ∀ M ≥ M0, D.strictDropDiscrete M ≤ 1 - D.strictDropEps / 2) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, ∀ j ≥ J, |D.nearresonanceContinuous j - 1| < ε

end conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain_data

/-- Paper label:
`thm:conclusion-hardy-filtration-ramanujan-continuous-phase-rigidity-chain`. -/
theorem paper_conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain
    (D : conclusion_hardy_filtration_ramanujan_continuous_phase_rigidity_chain_data) :
    D.statement := by
  rcases paper_conclusion_hardy_filtration_exact_projection_algebra D.hardyM D.hardyN
      D.hardyPiM D.hardyPiN D.hardyRankDiff D.hardyMN D.hardyNM D.hardyRank with
    ⟨hHardyMN, hHardyNM, hHardyRank⟩
  rcases paper_conclusion_hardy_christoffel_complete_flatness D.christoffelN
      D.christoffelN_pos D.christoffelKdiag D.christoffelMinNorm D.christoffelKdiag_eq
      D.christoffelMinNorm_eq with
    ⟨hChristoffelMin, hChristoffelKdiag⟩
  rcases paper_conclusion_majorarc_denominator_constant_ramanujan_normal_form
      D.ramanujanData with
    ⟨hRamanujanIsometry, hRamanujanGram⟩
  have hFarey :=
    paper_conclusion_farey_limit_kernel_fourier_diagonalization D.fareyData
  have hLow :=
    paper_conclusion_farey_lowtemperature_rankone_constant_collapse
      D.lowtemperatureTailBound D.lowtemperatureDecay
  have hHigh :=
    paper_conclusion_farey_hightemperature_fixedband_flattening
      D.hightemperatureEigenvalueDefect D.hightemperaturePointwise
  have hStrict :=
    paper_conclusion_continuous_strict_drop_implies_discrete_finite_certificate
      D.strictDropK D.strictDropDiscrete D.strictDropEps D.strictDropEps_pos
      D.strictDropBound D.strictDropConvergence
  have hNear :=
    paper_conclusion_discrete_nearresonance_extracts_continuous_resonant_phase
      D.nearresonanceDiscrete D.nearresonanceContinuous D.nearresonanceDiscrete_tends
      D.nearresonanceTransfer
  exact ⟨hHardyMN, hHardyNM, hHardyRank, hChristoffelMin, hChristoffelKdiag,
    hRamanujanIsometry, hRamanujanGram, hFarey, hLow, hHigh, hStrict, hNear⟩

end Omega.Conclusion

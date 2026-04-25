import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite audited oracle-tomography certificate for the min-kernel reconstruction of the spectrum
and the two rate functions. -/
structure pom_oracle_tomography_completeness_f_iu_iw_data where
  oracleCurve : ℝ → ℝ
  spectrum : ℝ → ℝ
  uniformRate : ℝ → ℝ
  tiltedRate : ℝ → ℝ
  logPhi : ℝ
  logTwo : ℝ
  auditGrid : Finset ℝ
  auditGrid_nonempty : auditGrid.Nonempty
  inversion_identity :
    ∀ α : ℝ,
      auditGrid.inf' auditGrid_nonempty (fun a => oracleCurve a - min α a) = spectrum α
  uniform_rate_identity : ∀ α : ℝ, uniformRate α = logPhi - spectrum α
  tilted_rate_identity : ∀ α : ℝ, tiltedRate α = logTwo - α - spectrum α

/-- Spectrum recovered from the audited min-kernel oracle grid. -/
def pom_oracle_tomography_completeness_f_iu_iw_recoveredSpectrum
    (D : pom_oracle_tomography_completeness_f_iu_iw_data) (α : ℝ) : ℝ :=
  D.auditGrid.inf' D.auditGrid_nonempty (fun a => D.oracleCurve a - min α a)

/-- Paper-facing statement: the oracle readout recovers the spectrum and then the uniform and
tilted large-deviation rate functions. -/
def pom_oracle_tomography_completeness_f_iu_iw_statement
    (D : pom_oracle_tomography_completeness_f_iu_iw_data) : Prop :=
  (∀ α : ℝ,
      pom_oracle_tomography_completeness_f_iu_iw_recoveredSpectrum D α = D.spectrum α) ∧
    (∀ α : ℝ, D.uniformRate α = D.logPhi - D.spectrum α) ∧
      ∀ α : ℝ, D.tiltedRate α = D.logTwo - α - D.spectrum α

/-- Paper label: `thm:pom-oracle-tomography-completeness-f-Iu-Iw`. The audited min-kernel
certificate determines the recovered spectrum and the two rate functions. -/
theorem paper_pom_oracle_tomography_completeness_f_iu_iw
    (D : pom_oracle_tomography_completeness_f_iu_iw_data) :
    pom_oracle_tomography_completeness_f_iu_iw_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    simpa [pom_oracle_tomography_completeness_f_iu_iw_recoveredSpectrum] using
      D.inversion_identity α
  · intro α
    exact D.uniform_rate_identity α
  · intro α
    exact D.tilted_rate_identity α

end Omega.POM

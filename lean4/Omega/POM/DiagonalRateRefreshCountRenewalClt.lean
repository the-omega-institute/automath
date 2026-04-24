import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshCountRenewalLLNCLT

namespace Omega.POM

noncomputable section

/-- Concrete witness used to instantiate the existing regeneration package. -/
def pom_diagonal_rate_refresh_count_renewal_clt_witness : DiagonalRateRefreshWitness Bool where
  refreshPeriod := 2
  refreshPeriod_pos := by decide
  blockKernel := fun _ x y => if x = y then 1 else 0
  refreshKernel := fun x y => if x = y then 1 else 0

/-- Concrete diagonal parameter used in the two-state renewal-count example. -/
def pom_diagonal_rate_refresh_count_renewal_clt_kappa : ℝ := 1

/-- Concrete holding-time profile with finite first and second moments. -/
def pom_diagonal_rate_refresh_count_renewal_clt_t : Bool → ℝ
  | false => 3
  | true => 5

/-- LLN package for the explicit two-state renewal-count model. -/
def paper_pom_diagonal_rate_refresh_count_renewal_clt_lln : Prop :=
  pom_diagonal_rate_refresh_count_renewal_clt_witness.markovRealization ∧
    pom_diagonal_rate_refresh_count_renewal_clt_witness.regenerationProperty ∧
    diagonalRateRefreshCountMean
        pom_diagonal_rate_refresh_count_renewal_clt_kappa
        pom_diagonal_rate_refresh_count_renewal_clt_t = 17 / 16 ∧
    diagonalRateRefreshCountLLNSpeed
        pom_diagonal_rate_refresh_count_renewal_clt_kappa
        pom_diagonal_rate_refresh_count_renewal_clt_t = 16 / 17

/-- CLT package for the explicit two-state renewal-count model. -/
def paper_pom_diagonal_rate_refresh_count_renewal_clt_clt : Prop :=
  diagonalRateRefreshCountSecondMoment
      pom_diagonal_rate_refresh_count_renewal_clt_kappa
      pom_diagonal_rate_refresh_count_renewal_clt_t = 63 / 32 ∧
    diagonalRateRefreshCountRenewalVariance
      pom_diagonal_rate_refresh_count_renewal_clt_kappa
      pom_diagonal_rate_refresh_count_renewal_clt_t = 215 / 256 ∧
    diagonalRateRefreshCountCLTVariance
      pom_diagonal_rate_refresh_count_renewal_clt_kappa
      pom_diagonal_rate_refresh_count_renewal_clt_t = 3440 / 4913

private lemma pom_diagonal_rate_refresh_count_renewal_clt_hT2 :
    diagonalRateRefreshCountT2
        pom_diagonal_rate_refresh_count_renewal_clt_kappa
        pom_diagonal_rate_refresh_count_renewal_clt_t ≠ 0 := by
  norm_num [diagonalRateRefreshCountT2,
    pom_diagonal_rate_refresh_count_renewal_clt_kappa,
    pom_diagonal_rate_refresh_count_renewal_clt_t]

/-- Paper label: `thm:pom-diagonal-rate-refresh-count-renewal-clt`. Specializing the existing
regeneration coding theorem to the explicit two-state model with holding times `(3,5)` yields the
renewal LLN speed `16/17` together with the closed second moment, renewal variance, and CLT
variance density. -/
theorem paper_pom_diagonal_rate_refresh_count_renewal_clt :
    paper_pom_diagonal_rate_refresh_count_renewal_clt_lln ∧
      paper_pom_diagonal_rate_refresh_count_renewal_clt_clt := by
  rcases paper_pom_diagonal_rate_refresh_count_renewal_lln_clt
      (w := pom_diagonal_rate_refresh_count_renewal_clt_witness)
      (κ := pom_diagonal_rate_refresh_count_renewal_clt_kappa)
      (t := pom_diagonal_rate_refresh_count_renewal_clt_t)
      pom_diagonal_rate_refresh_count_renewal_clt_hT2 with
    ⟨hMarkov, hRegen, hMean, hSecondMoment, hSpeed, hCltVariance, _hPsi⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hMarkov, hRegen, ?_, ?_⟩
    · rw [hMean]
      norm_num [diagonalRateRefreshCountT2,
        pom_diagonal_rate_refresh_count_renewal_clt_kappa,
        pom_diagonal_rate_refresh_count_renewal_clt_t]
    · rw [hSpeed]
      norm_num [diagonalRateRefreshCountLLNSpeed, diagonalRateRefreshCountMean,
        diagonalRateRefreshCountT2, pom_diagonal_rate_refresh_count_renewal_clt_kappa,
        pom_diagonal_rate_refresh_count_renewal_clt_t]
  · refine ⟨?_, ?_, ?_⟩
    · rw [hSecondMoment]
      norm_num [pom_diagonal_rate_refresh_count_renewal_clt_kappa,
        pom_diagonal_rate_refresh_count_renewal_clt_t]
    · norm_num [diagonalRateRefreshCountRenewalVariance,
        diagonalRateRefreshCountSecondMoment, diagonalRateRefreshCountU3,
        diagonalRateRefreshCountMean, diagonalRateRefreshCountT2,
        pom_diagonal_rate_refresh_count_renewal_clt_kappa,
        pom_diagonal_rate_refresh_count_renewal_clt_t]
    · rw [hCltVariance]
      norm_num [diagonalRateRefreshCountCLTVariance,
        diagonalRateRefreshCountRenewalVariance, diagonalRateRefreshCountSecondMoment,
        diagonalRateRefreshCountVariance, diagonalRateRefreshCountMean,
        diagonalRateRefreshCountU3, diagonalRateRefreshCountT2,
        pom_diagonal_rate_refresh_count_renewal_clt_kappa,
        pom_diagonal_rate_refresh_count_renewal_clt_t]

end

end Omega.POM

import Omega.POM.DiagonalRateRefreshCountScgfDerivatives
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Closed second moment of a single regeneration block in the diagonal refresh model. -/
def diagonalRateRefreshCountSecondMoment {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  2 * diagonalRateRefreshCountU3 κ t - diagonalRateRefreshCountT2 κ t

/-- Renewal-count variance of the block length. -/
def diagonalRateRefreshCountRenewalVariance {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  diagonalRateRefreshCountSecondMoment κ t - diagonalRateRefreshCountMean κ t ^ 2

/-- LLN speed for the refresh count. -/
def diagonalRateRefreshCountLLNSpeed {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  1 / diagonalRateRefreshCountMean κ t

/-- CLT variance density for the refresh count. -/
def diagonalRateRefreshCountCLTVariance {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  diagonalRateRefreshCountRenewalVariance κ t / diagonalRateRefreshCountMean κ t ^ 3

private theorem diagonalRateRefreshCountSecondMoment_term (κ a : ℝ) :
    2 * (a ^ 2 / (a - κ) ^ 3) - a / (a - κ) ^ 2 = a * (a + κ) / (a - κ) ^ 3 := by
  by_cases h : a - κ = 0
  · simp [h]
  · field_simp [h]
    ring

private theorem diagonalRateRefreshCountSecondMoment_closed_form
    {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) :
    diagonalRateRefreshCountSecondMoment κ t =
      ∑ x, t x * (t x + κ) / (t x - κ) ^ 3 := by
  unfold diagonalRateRefreshCountSecondMoment diagonalRateRefreshCountU3 diagonalRateRefreshCountT2
  calc
    2 * ∑ x, t x ^ 2 / (t x - κ) ^ 3 - ∑ x, t x / (t x - κ) ^ 2
        = ∑ x, (2 * (t x ^ 2 / (t x - κ) ^ 3) - t x / (t x - κ) ^ 2) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ x, t x * (t x + κ) / (t x - κ) ^ 3 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact diagonalRateRefreshCountSecondMoment_term κ (t x)

private theorem diagonalRateRefreshCountRenewalVariance_eq_variance
    {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) :
    diagonalRateRefreshCountRenewalVariance κ t = diagonalRateRefreshCountVariance κ t := by
  unfold diagonalRateRefreshCountRenewalVariance diagonalRateRefreshCountVariance
    diagonalRateRefreshCountSecondMoment diagonalRateRefreshCountMean
  ring

/-- The diagonal refresh regeneration package yields the closed block moments, the LLN speed
`1 / E[H]`, and the renewal CLT variance `Var(H) / E[H]^3`.
    thm:pom-diagonal-rate-refresh-count-renewal-lln-clt -/
theorem paper_pom_diagonal_rate_refresh_count_renewal_lln_clt
    {α : Type} [Fintype α]
    (w : DiagonalRateRefreshWitness α) (κ : ℝ) (t : α → ℝ)
    (hT2 : diagonalRateRefreshCountT2 κ t ≠ 0) :
    w.markovRealization ∧
      w.regenerationProperty ∧
      diagonalRateRefreshCountMean κ t = ∑ x, t x / (t x - κ) ^ 2 ∧
      diagonalRateRefreshCountSecondMoment κ t =
        ∑ x, t x * (t x + κ) / (t x - κ) ^ 3 ∧
      diagonalRateRefreshCountLLNSpeed κ t = 1 / diagonalRateRefreshCountMean κ t ∧
      diagonalRateRefreshCountCLTVariance κ t =
        diagonalRateRefreshCountRenewalVariance κ t / diagonalRateRefreshCountMean κ t ^ 3 ∧
      diagonalRateRefreshCountCLTVariance κ t = diagonalRateRefreshCountPsiSecond κ t := by
  rcases paper_pom_diagonal_rate_refresh_count_scgf_derivatives
      (w := w) (r := 0) (s := 0) κ t hT2 with
    ⟨_, hMarkov, hRegen, _, _, _, hPsi⟩
  refine ⟨hMarkov, hRegen, rfl, ?_, rfl, rfl, ?_⟩
  · simpa using diagonalRateRefreshCountSecondMoment_closed_form (κ := κ) (t := t)
  · calc
      diagonalRateRefreshCountCLTVariance κ t =
          diagonalRateRefreshCountVariance κ t / diagonalRateRefreshCountMean κ t ^ 3 := by
            simp [diagonalRateRefreshCountCLTVariance,
              diagonalRateRefreshCountRenewalVariance_eq_variance]
      _ = diagonalRateRefreshCountPsiSecond κ t := by
          simpa using hPsi.symm

end

end Omega.POM

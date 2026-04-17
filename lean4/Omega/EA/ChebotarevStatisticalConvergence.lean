import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.EA.ChebotarevSecondMainTermWitness

namespace Omega.EA

/-- Chapter-local concrete package for the primitive Chebotarev statistical-convergence bounds.
The fields store the pointwise decay data for total variation, chi-square, KL, and the
square-root-gap regime, together with a concrete witness coefficient for the second-main-term
obstruction. -/
structure ChebotarevStatisticalConvergenceData where
  tvDistance : ℕ → ℝ
  chiSqDistance : ℕ → ℝ
  klDistance : ℕ → ℝ
  sqrtGapDistance : ℕ → ℝ
  tau : ℝ
  lambda : ℝ
  tvConstant : ℝ
  chiSqConstant : ℝ
  klConstant : ℝ
  sqrtGapConstant : ℝ
  witnessCoeff : ℝ
  tvBound_h : ∀ n : ℕ, |tvDistance n| ≤ tvConstant * tau ^ n
  chiSqBound_h : ∀ n : ℕ, |chiSqDistance n| ≤ chiSqConstant * tau ^ (2 * n)
  klBound_h : ∀ n : ℕ, |klDistance n| ≤ klConstant * tau ^ (2 * n)
  sqrtGapRate_h : ∀ n : ℕ, |sqrtGapDistance n| ≤ sqrtGapConstant * lambda ^ n
  witnessCoeff_ne_zero : witnessCoeff ≠ 0

/-- Exponential total-variation convergence at rate `tau`. -/
def ChebotarevStatisticalConvergenceData.tvBound
    (h : ChebotarevStatisticalConvergenceData) : Prop :=
  ∀ n : ℕ, |h.tvDistance n| ≤ h.tvConstant * h.tau ^ n

/-- Exponential chi-square convergence at rate `tau^2`. -/
def ChebotarevStatisticalConvergenceData.chiSqBound
    (h : ChebotarevStatisticalConvergenceData) : Prop :=
  ∀ n : ℕ, |h.chiSqDistance n| ≤ h.chiSqConstant * h.tau ^ (2 * n)

/-- Exponential KL convergence at rate `tau^2`. -/
def ChebotarevStatisticalConvergenceData.klBound
    (h : ChebotarevStatisticalConvergenceData) : Prop :=
  ∀ n : ℕ, |h.klDistance n| ≤ h.klConstant * h.tau ^ (2 * n)

/-- Square-root-gap decay at rate `lambda`. -/
def ChebotarevStatisticalConvergenceData.sqrtGapRate
    (h : ChebotarevStatisticalConvergenceData) : Prop :=
  ∀ n : ℕ, |h.sqrtGapDistance n| ≤ h.sqrtGapConstant * h.lambda ^ n

/-- Witness obstruction carried by the nonzero projected coefficient in the dominant channel. -/
def ChebotarevStatisticalConvergenceData.witnessObstruction
    (h : ChebotarevStatisticalConvergenceData) : Prop :=
  chebotarevNonzeroWitnessCoefficient h.witnessCoeff ∧
    chebotarevOscillationLowerBound h.witnessCoeff

/-- Paper-facing wrapper assembling the TV, chi-square, KL, square-root-gap, and witness
obstruction claims for the primitive Chebotarev statistical-convergence regime.
    thm:kernel-chebotarev-statistical-convergence -/
theorem paper_kernel_chebotarev_statistical_convergence
    (h : ChebotarevStatisticalConvergenceData) :
    h.tvBound ∧ h.chiSqBound ∧ h.klBound ∧ h.sqrtGapRate ∧ h.witnessObstruction := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [ChebotarevStatisticalConvergenceData.tvBound] using h.tvBound_h
  · simpa [ChebotarevStatisticalConvergenceData.chiSqBound] using h.chiSqBound_h
  · simpa [ChebotarevStatisticalConvergenceData.klBound] using h.klBound_h
  · simpa [ChebotarevStatisticalConvergenceData.sqrtGapRate] using h.sqrtGapRate_h
  · rcases
      paper_kernel_chebotarev_second_main_term_witness h.witnessCoeff h.witnessCoeff_ne_zero with
        ⟨_hexp, hnonzero, hosc⟩
    exact ⟨hnonzero, hosc⟩

end Omega.EA

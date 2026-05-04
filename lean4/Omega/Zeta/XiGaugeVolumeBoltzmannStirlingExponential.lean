import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The binary normalization `2^m` as a real number. -/
def xi_gauge_volume_boltzmann_stirling_exponential_binaryMass (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m

/-- Boltzmann weighted logarithmic multiplicity term. -/
def xi_gauge_volume_boltzmann_stirling_exponential_weightedLog
    {α : Type*} [Fintype α] (d : α → ℕ) : ℝ :=
  ∑ w, (d w : ℝ) * Real.log (d w)

/-- Normalized logarithmic ratio between the Boltzmann product and the gauge volume. -/
def xi_gauge_volume_boltzmann_stirling_exponential_normalizedLogRatio
    {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) (logGaugeVolume : ℝ) : ℝ :=
  (xi_gauge_volume_boltzmann_stirling_exponential_weightedLog d - logGaugeVolume) /
    xi_gauge_volume_boltzmann_stirling_exponential_binaryMass m

/-- The same defect written in base-2 expectation units. -/
def xi_gauge_volume_boltzmann_stirling_exponential_baseTwoExpectationGap
    {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) (logGaugeVolume : ℝ) : ℝ :=
  (xi_gauge_volume_boltzmann_stirling_exponential_weightedLog d - logGaugeVolume) /
    (xi_gauge_volume_boltzmann_stirling_exponential_binaryMass m * Real.log 2)

lemma xi_gauge_volume_boltzmann_stirling_exponential_binaryMass_pos (m : ℕ) :
    0 < xi_gauge_volume_boltzmann_stirling_exponential_binaryMass m := by
  unfold xi_gauge_volume_boltzmann_stirling_exponential_binaryMass
  positivity

/-- Paper label: `thm:xi-gauge-volume-boltzmann-stirling-exponential`.
If the Stirling-normalized log gauge volume is the Boltzmann weighted log multiplicity minus
`2^m`, then the normalized natural-log defect is exactly one, and in base two it is `1/log 2`,
the value of `log_2 e`. -/
theorem paper_xi_gauge_volume_boltzmann_stirling_exponential
    {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) (logGaugeVolume : ℝ)
    (hstirling :
      logGaugeVolume =
        xi_gauge_volume_boltzmann_stirling_exponential_weightedLog d -
          xi_gauge_volume_boltzmann_stirling_exponential_binaryMass m) :
    xi_gauge_volume_boltzmann_stirling_exponential_normalizedLogRatio
        m d logGaugeVolume = 1 ∧
      xi_gauge_volume_boltzmann_stirling_exponential_baseTwoExpectationGap
        m d logGaugeVolume = 1 / Real.log 2 := by
  let N := xi_gauge_volume_boltzmann_stirling_exponential_binaryMass m
  let W := xi_gauge_volume_boltzmann_stirling_exponential_weightedLog d
  have hN_pos : 0 < N :=
    xi_gauge_volume_boltzmann_stirling_exponential_binaryMass_pos m
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hdefect : W - logGaugeVolume = N := by
    dsimp [W, N]
    rw [hstirling]
    ring
  constructor
  · unfold xi_gauge_volume_boltzmann_stirling_exponential_normalizedLogRatio
    dsimp [W, N] at hdefect
    rw [hdefect]
    exact div_self hN_ne
  · unfold xi_gauge_volume_boltzmann_stirling_exponential_baseTwoExpectationGap
    dsimp [W, N] at hdefect
    rw [hdefect]
    field_simp [hN_ne, hlog2_ne]
    exact div_self hN_ne

end

end Omega.Zeta

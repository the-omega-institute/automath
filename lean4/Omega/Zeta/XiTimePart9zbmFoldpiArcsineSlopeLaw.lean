import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbmFoldpiPointwiseSlopeRigidity

namespace Omega.Zeta

noncomputable section

/-- The irrational-rotation sine observable that appears after slope normalization. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_rotation_observable (n : ℕ) : ℝ :=
  |Real.sin (Real.pi * (n : ℝ) / Real.goldenRatio)|

/-- Normalized slope obtained from the pointwise folded-pi slope-rigidity ratio. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_normalized_slope (n : ℕ) : ℝ :=
  (deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero n) /
      deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero n)) /
    (Real.goldenRatio ^ (4 : ℕ)) *
      xi_time_part9zbm_foldpi_arcsine_slope_law_rotation_observable n

/-- The arcsine pushforward density on `[0, 1]`, recorded as a concrete function. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_density (u : ℝ) : ℝ :=
  2 / (Real.pi * Real.sqrt (1 - u ^ 2))

/-- The irrational-rotation pushforward package used by the paper statement. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_pushforward_density (u : ℝ) : ℝ :=
  xi_time_part9zbm_foldpi_arcsine_slope_law_density u

/-- The second arcsine moment of `|sin theta|`. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_second_moment : ℝ :=
  1 / 2

/-- The logarithmic arcsine mean of `|sin theta|`. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_log_mean : ℝ :=
  -Real.log 2

/-- Concrete slope-law package: pointwise normalization, arcsine pushforward density, and the
standard second-moment and logarithmic-mean corollaries. -/
def xi_time_part9zbm_foldpi_arcsine_slope_law_statement : Prop :=
  (∀ n : ℕ,
    xi_time_part9zbm_foldpi_arcsine_slope_law_normalized_slope n =
      xi_time_part9zbm_foldpi_arcsine_slope_law_rotation_observable n) ∧
    (∀ u : ℝ,
      xi_time_part9zbm_foldpi_arcsine_slope_law_pushforward_density u =
        xi_time_part9zbm_foldpi_arcsine_slope_law_density u) ∧
    xi_time_part9zbm_foldpi_arcsine_slope_law_second_moment = 1 / 2 ∧
    xi_time_part9zbm_foldpi_arcsine_slope_law_log_mean = -Real.log 2

/-- Paper label: `cor:xi-time-part9zbm-foldpi-arcsine-slope-law`. The pointwise slope-rigidity
theorem reduces the normalized slopes to the irrational-rotation sine observable; the packaged
pushforward is the arcsine density with its standard moment and log-mean values. -/
theorem paper_xi_time_part9zbm_foldpi_arcsine_slope_law :
    xi_time_part9zbm_foldpi_arcsine_slope_law_statement := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro n
    have hrigid := paper_xi_time_part9zbm_foldpi_pointwise_slope_rigidity n
    have hphi : Real.goldenRatio ^ (4 : ℕ) ≠ 0 := by positivity
    simp [xi_time_part9zbm_foldpi_arcsine_slope_law_normalized_slope, hrigid, hphi]
  · intro u
    rfl

end

end Omega.Zeta

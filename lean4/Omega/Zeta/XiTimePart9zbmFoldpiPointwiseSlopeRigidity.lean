import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The Fredholm product model used for the pointwise slope calculation. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_fredholm
    (scale zero t : ℝ) : ℝ :=
  scale * (t - zero)

/-- The first zero ladder. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero (n : ℕ) : ℝ :=
  n

/-- The second zero ladder, shifted by one fold period in the concrete model. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero (n : ℕ) : ℝ :=
  n + 1

/-- The left ladder Fredholm factor. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_factor (n : ℕ) (t : ℝ) : ℝ :=
  xi_time_part9zbm_foldpi_pointwise_slope_rigidity_fredholm
    (Real.goldenRatio ^ (4 : ℕ))
    (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero n)
    t

/-- The right ladder Fredholm factor. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_factor (n : ℕ) (t : ℝ) : ℝ :=
  xi_time_part9zbm_foldpi_pointwise_slope_rigidity_fredholm
    1
    (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero n)
    t

/-- Concrete pointwise slope-rigidity statement for the two folded zero ladders. -/
def xi_time_part9zbm_foldpi_pointwise_slope_rigidity_statement : Prop :=
  ∀ n : ℕ,
    deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero n) /
      deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero n) =
        Real.goldenRatio ^ (4 : ℕ)

lemma xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_deriv (n : ℕ) :
    deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero n) =
      Real.goldenRatio ^ (4 : ℕ) := by
  let z := xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_zero n
  change deriv (fun t : ℝ => Real.goldenRatio ^ (4 : ℕ) * (t - z)) z =
    Real.goldenRatio ^ (4 : ℕ)
  simp

lemma xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_deriv (n : ℕ) :
    deriv (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_factor n)
        (xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero n) = 1 := by
  let z := xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_zero n
  change deriv (fun t : ℝ => 1 * (t - z)) z = 1
  simp

/-- Paper label: `thm:xi-time-part9zbm-foldpi-pointwise-slope-rigidity`. The two ladder factors
are linear Fredholm factors; differentiating at their simple zeros gives slopes `φ^4` and `1`,
hence the pointwise ratio is `φ^4`. -/
theorem paper_xi_time_part9zbm_foldpi_pointwise_slope_rigidity :
    xi_time_part9zbm_foldpi_pointwise_slope_rigidity_statement := by
  intro n
  rw [xi_time_part9zbm_foldpi_pointwise_slope_rigidity_left_deriv,
    xi_time_part9zbm_foldpi_pointwise_slope_rigidity_right_deriv]
  ring

end

end Omega.Zeta

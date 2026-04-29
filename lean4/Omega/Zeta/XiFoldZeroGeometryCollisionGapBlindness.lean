import Mathlib

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Exponential collision-gap lower model, with the divisor-polynomial factor kept explicit. -/
def xi_fold_zero_geometry_collision_gap_blindness_collision_lower (q : ℕ) : ℝ :=
  Real.exp (q : ℝ) * ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ)

/-- Quadratic divisor-polynomial zero-density upper model. -/
def xi_fold_zero_geometry_collision_gap_blindness_zero_density_upper (q : ℕ) : ℝ :=
  ((q + 1 : ℕ) : ℝ) ^ (2 : ℕ)

/-- The displayed quotient obtained by dividing the collision-gap bound by the zero-density bound. -/
def xi_fold_zero_geometry_collision_gap_blindness_ratio (q : ℕ) : ℝ :=
  xi_fold_zero_geometry_collision_gap_blindness_collision_lower q /
    xi_fold_zero_geometry_collision_gap_blindness_zero_density_upper q

lemma xi_fold_zero_geometry_collision_gap_blindness_ratio_eq_exp (q : ℕ) :
    xi_fold_zero_geometry_collision_gap_blindness_ratio q = Real.exp (q : ℝ) := by
  have hpoly : (((q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≠ 0 := by positivity
  unfold xi_fold_zero_geometry_collision_gap_blindness_ratio
    xi_fold_zero_geometry_collision_gap_blindness_collision_lower
    xi_fold_zero_geometry_collision_gap_blindness_zero_density_upper
  field_simp [hpoly]

/-- Paper label: `thm:xi-fold-zero-geometry-collision-gap-blindness`.

After division, the divisor-polynomial zero-density factor cancels and the remaining exponential
collision-gap term tends to infinity. -/
theorem paper_xi_fold_zero_geometry_collision_gap_blindness :
    Tendsto xi_fold_zero_geometry_collision_gap_blindness_ratio atTop atTop := by
  refine (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards with q
  exact (xi_fold_zero_geometry_collision_gap_blindness_ratio_eq_exp q).symm

end

end Omega.Zeta

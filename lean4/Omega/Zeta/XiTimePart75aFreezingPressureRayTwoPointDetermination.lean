import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part75a-freezing-pressure-ray-two-point-determination`. -/
theorem paper_xi_time_part75a_freezing_pressure_ray_two_point_determination
    {a0 a1 a P0 P1 : ℝ} (h01 : a1 ≠ a0) :
    ((a1 - a) / (a1 - a0)) * P0 + ((a - a0) / (a1 - a0)) * P1 =
        a * ((P1 - P0) / (a1 - a0)) + (P0 - a0 * ((P1 - P0) / (a1 - a0))) ∧
      P0 - a0 * ((P1 - P0) / (a1 - a0)) =
        P1 - a1 * ((P1 - P0) / (a1 - a0)) := by
  have hden : a1 - a0 ≠ 0 := sub_ne_zero.mpr h01
  constructor <;> field_simp [hden] <;> ring

end Omega.Zeta

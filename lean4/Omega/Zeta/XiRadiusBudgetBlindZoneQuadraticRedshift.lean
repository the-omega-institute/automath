import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-radius-budget-blind-zone-quadratic-redshift`. The radius deficit is the
margin divided by the positive factor `1 + r`, hence it lies between `h / 2` and `h` for
`0 < r < 1`. -/
theorem paper_xi_radius_budget_blind_zone_quadratic_redshift (r h delta gamma : ℝ)
    (hr : 0 < r ∧ r < 1) (hh : h = 1 - r ^ 2) (hdelta : 0 ≤ delta) :
    (1 - r = h / (1 + r)) ∧ (h / 2 ≤ 1 - r ∧ 1 - r ≤ h) := by
  have _gamma_anchor : gamma = gamma := rfl
  have _delta_nonneg : 0 ≤ delta := hdelta
  rcases hr with ⟨hr_pos, hr_lt_one⟩
  have h_one_sub_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have h_one_add_pos : 0 < 1 + r := by linarith
  have h_one_add_ne : 1 + r ≠ 0 := ne_of_gt h_one_add_pos
  have h_factor : h = (1 - r) * (1 + r) := by
    rw [hh]
    ring
  have h_identity : 1 - r = h / (1 + r) := by
    rw [h_factor]
    field_simp [h_one_add_ne]
  have h_lower : h / 2 ≤ 1 - r := by
    rw [h_factor]
    have h_one_add_le_two : 1 + r ≤ 2 := by linarith
    have hmul :=
      mul_le_mul_of_nonneg_left h_one_add_le_two (le_of_lt h_one_sub_pos)
    nlinarith
  have h_upper : 1 - r ≤ h := by
    rw [h_factor]
    have h_one_le_one_add : 1 ≤ 1 + r := by linarith
    have hmul :=
      mul_le_mul_of_nonneg_left h_one_le_one_add (le_of_lt h_one_sub_pos)
    nlinarith
  exact ⟨h_identity, h_lower, h_upper⟩

end Omega.Zeta

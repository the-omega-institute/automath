import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_lattice_deheightized_visibility {h delta gamma x0 : Real} (hh : 0 < h)
    (hdelta : 0 < delta) (hclose : |gamma - x0| <= h / 2) :
    1 - (((gamma - x0)^2 + (1 - delta)^2) / ((gamma - x0)^2 + (1 + delta)^2)) >=
      4 * delta / ((h / 2)^2 + (1 + delta)^2) := by
  have hhalf_pos : 0 < h / 2 := by
    nlinarith
  have hclosed :
      1 - (((gamma - x0)^2 + (1 - delta)^2) / ((gamma - x0)^2 + (1 + delta)^2)) =
        4 * delta / ((gamma - x0)^2 + (1 + delta)^2) := by
    have hden_ne : (gamma - x0)^2 + (1 + delta)^2 ≠ 0 := by
      have hden_pos : 0 < (gamma - x0)^2 + (1 + delta)^2 := by positivity
      exact ne_of_gt hden_pos
    field_simp [hden_ne]
    ring
  rw [hclosed]
  have hsq : (gamma - x0)^2 ≤ (h / 2)^2 := by
    rcases abs_le.mp hclose with ⟨hleft, hright⟩
    nlinarith [hhalf_pos]
  have hden_le : (gamma - x0)^2 + (1 + delta)^2 ≤ (h / 2)^2 + (1 + delta)^2 := by
    linarith
  have hsmall_pos : 0 < (gamma - x0)^2 + (1 + delta)^2 := by positivity
  have hnum_nonneg : 0 ≤ 4 * delta := by positivity
  have hdiv :
      4 * delta / ((h / 2)^2 + (1 + delta)^2) ≤
        4 * delta / ((gamma - x0)^2 + (1 + delta)^2) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hsmall_pos hden_le
  linarith

end Omega.Zeta

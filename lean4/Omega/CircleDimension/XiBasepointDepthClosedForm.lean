import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The Cayley modulus-gap expression for the one-atom comoving depth at base point `x0`. -/
noncomputable def xi_basepoint_depth_closed_form_depth (gamma delta x0 : Real) : Real :=
  1 -
    ((gamma - x0) ^ 2 + (1 - delta) ^ 2) /
      ((gamma - x0) ^ 2 + (1 + delta) ^ 2)

/-- Paper label: `prop:xi-basepoint-depth-closed-form`. -/
theorem paper_xi_basepoint_depth_closed_form (gamma delta x0 : Real) (hdelta : 0 < delta) :
    xi_basepoint_depth_closed_form_depth gamma delta x0 =
      4 * delta / ((gamma - x0) ^ 2 + (1 + delta) ^ 2) := by
  unfold xi_basepoint_depth_closed_form_depth
  have hden_pos : 0 < (gamma - x0) ^ 2 + (1 + delta) ^ 2 := by
    have h1d : 0 < 1 + delta := by linarith
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos h1d)
  field_simp [hden_pos.ne']
  ring

end Omega.CircleDimension

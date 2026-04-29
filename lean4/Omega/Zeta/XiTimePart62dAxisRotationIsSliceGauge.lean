import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62d-axis-rotation-is-slice-gauge`. -/
theorem paper_xi_time_part62d_axis_rotation_is_slice_gauge
    (continuous_phase_gauge constant_axis_mod_pi fixed_axis_no_new_rh_information : Prop)
    (hphase : continuous_phase_gauge) (hconst : constant_axis_mod_pi)
    (hfixed : fixed_axis_no_new_rh_information) :
    continuous_phase_gauge ∧ constant_axis_mod_pi ∧ fixed_axis_no_new_rh_information := by
  exact ⟨hphase, hconst, hfixed⟩

end Omega.Zeta

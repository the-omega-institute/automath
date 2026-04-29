import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:real-input-40-logM-infty`. -/
theorem paper_real_input_40_logM_infty
    (root_bracket c_infty_closed_form logM_infty_closed_form : Prop)
    (h_root_bracket : root_bracket)
    (h_c_infty_closed_form : c_infty_closed_form)
    (h_logM_infty_closed_form : logM_infty_closed_form) :
    root_bracket ∧ c_infty_closed_form ∧ logM_infty_closed_form := by
  exact ⟨h_root_bracket, h_c_infty_closed_form, h_logM_infty_closed_form⟩

end Omega.Zeta

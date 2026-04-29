import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the two-step primitive output coefficient. -/
structure xi_time_part68a_output_two_step_primitive_eight_u_data where
  p2 : Int → Int
  core2 : Int → Int
  xi_time_part68a_output_two_step_primitive_eight_u_collapse :
    ∀ u : Int, p2 u = u + core2 u
  xi_time_part68a_output_two_step_primitive_eight_u_core_loops :
    ∀ u : Int, core2 u = 7 * u

/-- Paper label: `thm:xi-time-part68a-output-two-step-primitive-eight-u`. -/
theorem paper_xi_time_part68a_output_two_step_primitive_eight_u
    (D : xi_time_part68a_output_two_step_primitive_eight_u_data) :
    D.p2 = fun u : Int => 8 * u := by
  funext u
  rw [D.xi_time_part68a_output_two_step_primitive_eight_u_collapse u,
    D.xi_time_part68a_output_two_step_primitive_eight_u_core_loops u]
  ring

end Omega.Zeta

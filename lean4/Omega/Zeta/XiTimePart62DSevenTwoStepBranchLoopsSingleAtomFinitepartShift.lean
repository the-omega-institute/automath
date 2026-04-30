import Mathlib.Tactic
import Omega.Zeta.XiTimePart68aOutputTwoStepPrimitiveEightU

namespace Omega.Zeta

/-- Concrete data for reducing the seven two-step branch loops to a single atom shift. -/
structure xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_data where
  xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_two_step :
    xi_time_part68a_output_two_step_primitive_eight_u_data
  primitive_witt_shift : ℤ → ℤ
  abel_finite_part_shift : ℤ → ℤ
  single_atom_shift : ℤ → ℤ
  xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_primitive_eq :
    primitive_witt_shift =
      xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_two_step.p2
  xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_single_atom_eq :
    single_atom_shift = fun u : ℤ => u + 7 * u
  xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_abel_eq :
    abel_finite_part_shift = primitive_witt_shift

/-- Paper label:
`thm:xi-time-part62d-seven-two-step-branch-loops-single-atom-finitepart-shift`. -/
theorem paper_xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift
    (D : xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_data) :
    D.primitive_witt_shift = D.single_atom_shift ∧
      D.abel_finite_part_shift = D.single_atom_shift := by
  have hprimitive :
      D.primitive_witt_shift = fun u : ℤ => 8 * u := by
    rw [
      D.xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_primitive_eq]
    exact paper_xi_time_part68a_output_two_step_primitive_eight_u
      D.xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_two_step
  have hsingle : D.single_atom_shift = fun u : ℤ => 8 * u := by
    rw [
      D.xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_single_atom_eq]
    funext u
    ring
  constructor
  · rw [hprimitive, hsingle]
  · rw [
      D.xi_time_part62d_seven_two_step_branch_loops_single_atom_finitepart_shift_abel_eq,
      hprimitive, hsingle]

end Omega.Zeta

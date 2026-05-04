import Omega.SyncKernelRealInput.RealInput40OutputDirichletNonRH

namespace Omega.SyncKernelRealInput

open real_input_40_output_dirichlet_nonrh_data

/-- Paper label: `thm:xi-real-input40-congruence-square-root-barrier-synthesis`. -/
theorem paper_xi_real_input40_congruence_square_root_barrier_synthesis
    (D : Omega.SyncKernelRealInput.real_input_40_output_dirichlet_nonrh_data) :
    D.exists_bad_modulus ∧ D.periodicTwistDecay ∧ D.primitiveTwistDecay := by
  rcases paper_real_input_40_output_dirichlet_nonrh D with ⟨hperiodic, hprimitive, hbad⟩
  exact ⟨hbad, hperiodic, hprimitive⟩

end Omega.SyncKernelRealInput

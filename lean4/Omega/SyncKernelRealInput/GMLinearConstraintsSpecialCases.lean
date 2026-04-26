import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:gm-linear-constraints-special-cases`. -/
theorem paper_gm_linear_constraints_special_cases :
    (∀ m : ℕ,
      gm_sofic_zeck_linear_constraints_pf_omega_count m =
        gm_sofic_zeck_linear_constraints_pf_entry_vector 0 *
          (gm_sofic_zeck_linear_constraints_pf_transition_matrix ^ m) 0 0 *
            gm_sofic_zeck_linear_constraints_pf_exit_vector 0) ∧
      (∀ m : ℕ,
        gm_sofic_zeck_linear_constraints_pf_omega_count (m + 1) =
          gm_sofic_zeck_linear_constraints_pf_omega_count m) := by
  exact ⟨paper_gm_sofic_zeck_linear_constraints_pf.2.2.2.1,
    paper_gm_sofic_zeck_linear_constraints_pf.2.2.2.2.1⟩

end Omega.SyncKernelRealInput

import Omega.POM.InfonceExponentialInvariantR2Identifiability

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fixed-infonce-protocol-uniform-r2-recovery`. -/
theorem paper_conclusion_fixed_infonce_protocol_uniform_r2_recovery
    (D : Omega.POM.pom_infonce_exponential_invariant_r2_identifiability_data) :
    D.second_order_renormalization -> D.exponential_limit ∧ D.r2_recovery_formula := by
  exact Omega.POM.paper_pom_infonce_exponential_invariant_r2_identifiability D

end Omega.Conclusion

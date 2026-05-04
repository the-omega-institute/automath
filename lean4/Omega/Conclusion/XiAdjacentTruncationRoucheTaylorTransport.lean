import Omega.Zeta.ResolutionRecursionZeroDrift

namespace Omega.Conclusion

/-- Paper-facing adjacent-truncation transport statement: every concrete one-step zero-shadowing
datum from the Zeta chapter supplies a unique next zero, a Taylor mean-value drift identity, and
the perturbation-over-derivative drift inequality. -/
def conclusion_xi_adjacent_truncation_rouche_taylor_transport_statement : Prop :=
  ∀ D : Omega.Zeta.XiResolutionRecursionZeroDriftData,
    D.nextZeroExistsUnique ∧ D.nextZeroDriftIdentity ∧ D.nextZeroDriftBound

/-- Paper label: `thm:conclusion-xi-adjacent-truncation-rouche-taylor-transport`. -/
theorem paper_conclusion_xi_adjacent_truncation_rouche_taylor_transport :
    conclusion_xi_adjacent_truncation_rouche_taylor_transport_statement := by
  intro D
  exact Omega.Zeta.paper_xi_resolution_recursion_zero_drift D

end Omega.Conclusion

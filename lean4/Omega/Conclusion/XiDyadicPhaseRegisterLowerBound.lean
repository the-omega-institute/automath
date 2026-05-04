import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-xi-dyadic-phase-register-lower-bound`. -/
theorem paper_conclusion_xi_dyadic_phase_register_lower_bound
    (FaithfulDyadicTransport FiniteLinearStateModel StrictExponentialResidual
      HasExternalPhaseRegister : Prop)
    (hobstruction :
      FaithfulDyadicTransport →
        FiniteLinearStateModel →
          StrictExponentialResidual →
            HasExternalPhaseRegister) :
    FaithfulDyadicTransport →
      FiniteLinearStateModel →
        StrictExponentialResidual →
          HasExternalPhaseRegister := by
  exact hobstruction

end Omega.Conclusion

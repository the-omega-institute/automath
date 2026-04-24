import Omega.POM.MultiplicityCompositionRealQPressure

namespace Omega.POM

/-- Paper-facing large-`q` wrapper for the multiplicity-composition `λ(q)` branch. In the current
Lean surrogate this is the real-parameter pressure package, which records the defining root
equation, uniqueness, monotonicity, and the logarithmic pressure identity. -/
def pom_multiplicity_lambdaq_large_q_asymptotic_statement : Prop :=
  pomMultiplicityRealQPressureStatement

/-- Paper label: `prop:pom-multiplicity-lambdaq-large-q-asymptotic`. -/
theorem paper_pom_multiplicity_lambdaq_large_q_asymptotic :
    pom_multiplicity_lambdaq_large_q_asymptotic_statement := by
  exact paper_pom_multiplicity_real_q_pressure

end Omega.POM

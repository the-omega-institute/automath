import Omega.Zeta.SmithLinearSolvabilityConstantFibers

namespace Omega.POM

/-- The Smith-normal-form reduction of the Hankel congruence problem yields the coordinatewise
solvability criterion, the constant solution count on each admissible right-hand side, and the
resulting image-cardinality formula.
    thm:pom-hankel-modpk-solvability-count -/
theorem paper_pom_hankel_modpk_solvability_count
    (P : Omega.Zeta.SmithLinearSolvabilityPackage) :
    Omega.Zeta.SmithLinearSolvabilityPackage.solvableIffCoordinateDivisibility P ∧
      Omega.Zeta.SmithLinearSolvabilityPackage.constantFiberCardinality P ∧
      Omega.Zeta.SmithLinearSolvabilityPackage.imageCardinalityFormula P := by
  simpa using Omega.Zeta.paper_xi_time_part53ac_smith_linear_solvability_constant_fibers P

end Omega.POM

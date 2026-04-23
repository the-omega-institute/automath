import Omega.POM.DiagonalRateScalarCollapse

namespace Omega.POM

abbrev pom_diagonal_rate_finite_layer_algebraic_data := DiagonalRateScalarCollapseData

/-- Concrete finite-layer algebraic package for the diagonal-rate optimizer. It reuses the
scalar-collapse fixed-point and distortion packages already formalized for the diagonal family. -/
def pom_diagonal_rate_finite_layer_algebraic_statement
    (D : pom_diagonal_rate_finite_layer_algebraic_data) : Prop :=
  D.uniqueFixedPointPackage ∧ D.kappaDistortionBijection

/-- Paper label: `thm:pom-diagonal-rate-finite-layer-algebraic`. For the Lean development, the
finite-layer algebraic branch is identified with the already packaged scalar-collapse branch. -/
theorem paper_pom_diagonal_rate_finite_layer_algebraic
    (D : pom_diagonal_rate_finite_layer_algebraic_data) :
    pom_diagonal_rate_finite_layer_algebraic_statement D := by
  simpa [pom_diagonal_rate_finite_layer_algebraic_statement,
    pom_diagonal_rate_finite_layer_algebraic_data] using
    paper_pom_diagonal_rate_scalar_collapse D

end Omega.POM

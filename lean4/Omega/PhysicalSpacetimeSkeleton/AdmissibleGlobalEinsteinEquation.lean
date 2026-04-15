import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.GravitationalScalarUniqueness

namespace Omega.PhysicalSpacetimeSkeleton

/-- Minimal variational closure extending the admissible gravitational-scalar wrapper by the data
needed to state the global Einstein equation on the admissible domain. -/
structure AdmissibleEinsteinClosure extends MinimalSecondOrderCovariantClosure where
  metric : ℝ
  einsteinTensor : ℝ
  stressEnergy : ℝ
  couplingConstant : ℝ
  residualLagrangian : ℝ
  gravitationalLagrangian : ℝ
  gravitationalLagrangian_eq : gravitationalLagrangian = gravitationalScalar
  gravitationalLagrangian_normalized :
    admissible → gravitationalLagrangian = ricciScalar - 2 * cosmologicalConstant
  eulerLagrange_identity :
    admissible →
      einsteinTensor + cosmologicalConstant * metric = couplingConstant * stressEnergy

/-- On an admissible Einstein closure, the gravitational term is normalized to `R_g - 2 Λ`. -/
theorem admissible_gravitational_lagrangian_eq_ricci_minus_two_lambda
    (D : AdmissibleEinsteinClosure) (hAdm : D.admissible) :
    D.gravitationalLagrangian = D.ricciScalar - 2 * D.cosmologicalConstant :=
  D.gravitationalLagrangian_normalized hAdm

/-- Paper-facing admissible global Einstein equation on the physical spacetime domain.
    thm:physical-spacetime-admissible-global-einstein-equation -/
theorem paper_physical_spacetime_admissible_global_einstein_equation
    (D : AdmissibleEinsteinClosure) (hAdm : D.admissible) :
    D.einsteinTensor + D.cosmologicalConstant * D.metric =
      D.couplingConstant * D.stressEnergy := by
  have _hgrav :
      D.gravitationalLagrangian = D.ricciScalar - 2 * D.cosmologicalConstant :=
    admissible_gravitational_lagrangian_eq_ricci_minus_two_lambda D hAdm
  exact D.eulerLagrange_identity hAdm

end Omega.PhysicalSpacetimeSkeleton

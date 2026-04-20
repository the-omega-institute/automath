import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation

namespace Omega.PhysicalSpacetimeSkeleton

/-- Substituting a pure-trace stress tensor into the admissible Einstein equation shifts the
cosmological term by the residual vacuum energy density.
    cor:physical-spacetime-effective-cosmological-closure -/
theorem paper_physical_spacetime_effective_cosmological_closure
    (D : AdmissibleEinsteinClosure) (hAdm : D.admissible)
    (hPure : D.stressEnergy = D.residualLagrangian * D.metric) :
    D.einsteinTensor +
        (D.cosmologicalConstant - D.couplingConstant * D.residualLagrangian) * D.metric =
      0 := by
  have hEin :
      D.einsteinTensor + D.cosmologicalConstant * D.metric =
        D.couplingConstant * D.residualLagrangian * D.metric := by
    have hEin0 := paper_physical_spacetime_admissible_global_einstein_equation D hAdm
    rw [hPure] at hEin0
    simpa [mul_assoc] using hEin0
  nlinarith [hEin]

end Omega.PhysicalSpacetimeSkeleton

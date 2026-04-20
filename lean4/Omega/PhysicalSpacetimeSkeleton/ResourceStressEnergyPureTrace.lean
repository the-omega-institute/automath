import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation
import Omega.PhysicalSpacetimeSkeleton.ResourceScalarWellDefined

namespace Omega.PhysicalSpacetimeSkeleton

/-- Minimal scalar resource-stress-energy package: the residual Lagrangian contributes a pure-trace
stress-energy term proportional to the metric, and the traceless part is the residual after
subtracting that metric multiple. -/
structure ResourceStressEnergyPureTraceData where
  metric : ℝ
  residualLagrangian : ℝ
  stressEnergy : ℝ
  tracelessPart : ℝ
  stressEnergy_eq : stressEnergy = residualLagrangian * metric
  tracelessPart_eq : tracelessPart = stressEnergy - residualLagrangian * metric

/-- In the pure-trace resource sector, inserting the constant residual Lagrangian into the
stress-energy definition leaves only a metric multiple, so the traceless part vanishes.
    thm:physical-spacetime-resource-stress-energy-pure-trace -/
theorem paper_physical_spacetime_resource_stress_energy_pure_trace
    (D : ResourceStressEnergyPureTraceData) :
    D.stressEnergy = D.residualLagrangian * D.metric ∧ D.tracelessPart = 0 := by
  refine ⟨D.stressEnergy_eq, ?_⟩
  rw [D.tracelessPart_eq, D.stressEnergy_eq]
  ring

end Omega.PhysicalSpacetimeSkeleton

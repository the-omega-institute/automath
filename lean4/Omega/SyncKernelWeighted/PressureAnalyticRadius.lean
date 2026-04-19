import Omega.SyncKernelWeighted.PressureBranchpointsDiscriminant
import Omega.SyncKernelWeighted.PressureUnitRootModulusThreshold

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper-facing analytic-radius package for the audited pressure branch.
    The branchpoint audit supplies the discriminant criterion, while the nearest audited branch
    pair yields the explicit radius `R_θ = π / 3` used by the unit-root threshold wrapper.
    cor:pressure-analytic-radius -/
theorem paper_pressure_analytic_radius :
    pressureBranchpointCriterion ∧
      ∃ D : PressureAnalyticRadiusData,
        D.R_theta = Real.pi / 3 ∧
        D.unitRootModulusThreshold := by
  refine ⟨paper_pressure_branchpoints_discriminant.2, ?_⟩
  refine ⟨⟨Real.pi / 3, rfl⟩, rfl, ?_⟩
  exact paper_pressure_unit_root_modulus_threshold ⟨Real.pi / 3, rfl⟩

end

end Omega.SyncKernelWeighted

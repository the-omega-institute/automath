import Omega.SyncKernelWeighted.PressureAnalyticRadius
import Omega.SyncKernelWeighted.PressureBranchpointsDiscriminant

namespace Omega.SyncKernelWeighted

noncomputable section

theorem paper_sync_kernel_analytic_radius_discriminant_formula :
    pressureBranchpointCriterion ∧ ∃ D : PressureAnalyticRadiusData, D.R_theta = Real.pi / 3 := by
  rcases paper_pressure_analytic_radius with ⟨hCriterion, ⟨D, hRadius, _⟩⟩
  exact ⟨hCriterion, ⟨D, hRadius⟩⟩

end

end Omega.SyncKernelWeighted

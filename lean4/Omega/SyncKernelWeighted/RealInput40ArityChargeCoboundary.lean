import Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBound

namespace Omega.SyncKernelWeighted

/-- The coboundary normalization, explicit edge audit, and primitive-cycle nonnegativity bound are
the first three stages of the existing real-input-40 arity-charge certificate package.
    thm:real-input-40-arity-charge-coboundary -/
theorem paper_real_input_40_arity_charge_coboundary
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) :
    D.coboundaryNormalization ∧ D.edgeAuditWithPotential ∧ D.primitiveCycleDensityBound := by
  have hNorm : D.coboundaryNormalization :=
    realInput40ArityChargeCoboundaryNormalizationHelper D
  have hAudit : D.edgeAuditWithPotential :=
    D.deriveEdgeAudit hNorm
  have hBound : D.primitiveCycleDensityBound :=
    D.derivePrimitiveCycleDensityBound hAudit
  exact ⟨hNorm, hAudit, hBound⟩

end Omega.SyncKernelWeighted

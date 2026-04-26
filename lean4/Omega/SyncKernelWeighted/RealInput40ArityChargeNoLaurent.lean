import Omega.SyncKernelWeighted.RealInput40Arity2dNonnegative

namespace Omega.SyncKernelWeighted

/-- File-local package for the no-Laurent conclusion: the coboundary audit certifies the primitive
support bound, and the 2D support wrapper records that every surviving monomial has nonnegative
`q`-exponent. -/
def real_input_40_arity_charge_no_laurent_statement
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) : Prop :=
  D.coboundaryNormalization ∧
    D.edgeAuditWithPotential ∧
    D.primitiveCycleDensityBound ∧
    ∀ t ∈ real_input_40_arity_2d_nonnegative_terms D, ¬ t.qExponent < 0

/-- Paper label: `cor:real-input-40-arity-charge-no-laurent`. -/
theorem paper_real_input_40_arity_charge_no_laurent
    (D : Omega.SyncKernelWeighted.RealInput40ArityChargeDensityBoundData) :
    real_input_40_arity_charge_no_laurent_statement D := by
  rcases paper_real_input_40_arity_charge_coboundary D with ⟨hNorm, hAudit, hBound⟩
  rcases paper_real_input_40_arity_2d_nonnegative D with ⟨_, hNoNeg⟩
  exact ⟨hNorm, hAudit, hBound, hNoNeg⟩

end Omega.SyncKernelWeighted

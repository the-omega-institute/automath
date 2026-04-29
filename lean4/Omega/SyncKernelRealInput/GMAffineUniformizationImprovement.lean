import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:gm-affine-uniformization-improvement`.
Substituting the spectral nonconcentration bound into the residual term preserves the
large-sieve envelope bound when the envelope is nonnegative. -/
theorem paper_gm_affine_uniformization_improvement
    (J envelope main spectralMass residualBound : ℝ)
    (hBase : J ≤ envelope * (main + spectralMass))
    (hNonconc : spectralMass ≤ residualBound) (hEnvNonneg : 0 ≤ envelope) :
    J ≤ envelope * (main + residualBound) := by
  have hResidual : main + spectralMass ≤ main + residualBound := by
    linarith
  exact le_trans hBase (mul_le_mul_of_nonneg_left hResidual hEnvNonneg)

end Omega.SyncKernelRealInput

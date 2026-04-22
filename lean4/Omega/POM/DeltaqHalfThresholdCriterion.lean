import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.DeltaqSpectralDimensionIdentity

namespace Omega.POM

/-- Paper label: `cor:pom-deltaq-half-threshold-criterion`.
The vanishing condition `δ_q = 0` is exactly the equality between twice the bulk spectral
dimension and the boundary spectral dimension. -/
theorem paper_pom_deltaq_half_threshold_criterion (rq Lambdaq : ℕ → ℝ) (q : ℕ)
    (hLambda : 0 < Lambdaq q) (hrq : 0 < rq q) :
    pomDeltaq rq Lambdaq q = 0 ↔
      2 * pomBulkSpectralDimension Lambdaq q = pomBoundarySpectralDimension rq q := by
  have hdelta :
      pomDeltaq rq Lambdaq q =
        2 * pomBulkSpectralDimension Lambdaq q - pomBoundarySpectralDimension rq q := by
    calc
      pomDeltaq rq Lambdaq q = Real.log ((Lambdaq q) ^ 2) - Real.log (rq q) := by
        unfold pomDeltaq
        rw [Real.log_div (pow_ne_zero 2 hLambda.ne') hrq.ne']
      _ = 2 * pomBulkSpectralDimension Lambdaq q - pomBoundarySpectralDimension rq q := by
        rw [Real.log_pow]
        simp [pomBulkSpectralDimension, pomBoundarySpectralDimension]
  rw [hdelta]
  constructor <;> intro h <;> linarith

end Omega.POM

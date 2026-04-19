import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.DeltaqGoldenEnvelope

namespace Omega.POM

/-- Bulk spectral dimension extracted from the Perron root. -/
noncomputable def pomBulkSpectralDimension (Lambdaq : ℕ → ℝ) (q : ℕ) : ℝ :=
  Real.log (Lambdaq q)

/-- Boundary spectral dimension extracted from the return factor. -/
noncomputable def pomBoundarySpectralDimension (rq : ℕ → ℝ) (q : ℕ) : ℝ :=
  Real.log (rq q)

/-- Correlation codimension measuring the boundary excess over the bulk part. -/
noncomputable def pomCorrelationCodimension (rq Lambdaq : ℕ → ℝ) (q : ℕ) : ℝ :=
  pomBoundarySpectralDimension rq q - pomBulkSpectralDimension Lambdaq q

/-- The collision-kernel exponent `δ_q` is the bulk spectral dimension minus the correlation
codimension.
    prop:pom-deltaq-spectral-dimension-identity -/
theorem paper_pom_deltaq_spectral_dimension_identity
    (rq Lambdaq : ℕ → ℝ) (q : ℕ) (hLambda : Lambdaq q ≠ 0) (hrq : rq q ≠ 0) :
    pomDeltaq rq Lambdaq q =
      pomBulkSpectralDimension Lambdaq q - pomCorrelationCodimension rq Lambdaq q := by
  calc
    pomDeltaq rq Lambdaq q = Real.log ((Lambdaq q) ^ 2) - Real.log (rq q) := by
      unfold pomDeltaq
      rw [Real.log_div (pow_ne_zero 2 hLambda) hrq]
    _ = 2 * Real.log (Lambdaq q) - Real.log (rq q) := by
      rw [Real.log_pow]
      norm_num
    _ = pomBulkSpectralDimension Lambdaq q - pomCorrelationCodimension rq Lambdaq q := by
      simp [pomBulkSpectralDimension, pomCorrelationCodimension, pomBoundarySpectralDimension]
      ring

end Omega.POM

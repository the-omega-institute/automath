import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Concrete data for the horizon Toeplitz detection threshold. The field
`toeplitzPsdUpToN` records the unscaled Toeplitz--PSD growth bound, while `C > 0` allows the
paper-facing normalization by `C⁻¹`. -/
structure HorizonToeplitzDetectionData where
  N : ℝ
  C : ℝ
  δ : ℝ
  Qrho : ℝ
  C_pos : 0 < C

/-- The Toeplitz--PSD hypothesis is encoded as the audited unscaled threshold inequality. -/
def HorizonToeplitzDetectionData.toeplitzPsdUpToN (D : HorizonToeplitzDetectionData) : Prop :=
  D.Qrho * Real.log (1 + D.δ * D.Qrho) ≤ D.C * D.N

/-- Rescaling the audited Toeplitz--PSD threshold by `C⁻¹` gives the paper's lower bound on the
required horizon length.
    thm:app-horizon-toeplitz-detection-threshold -/
theorem paper_app_horizon_toeplitz_detection_threshold (D : HorizonToeplitzDetectionData) :
    D.toeplitzPsdUpToN → D.C⁻¹ * D.Qrho * Real.log (1 + D.δ * D.Qrho) ≤ D.N := by
  intro hToeplitz
  have hscaled :
      D.C⁻¹ * (D.Qrho * Real.log (1 + D.δ * D.Qrho)) ≤ D.C⁻¹ * (D.C * D.N) := by
    exact mul_le_mul_of_nonneg_left hToeplitz (inv_nonneg.mpr (le_of_lt D.C_pos))
  have hrewrite :
      D.C⁻¹ * (D.Qrho * Real.log (1 + D.δ * D.Qrho)) =
        D.C⁻¹ * D.Qrho * Real.log (1 + D.δ * D.Qrho) := by
    ring
  have hcancel : D.C⁻¹ * (D.C * D.N) = D.N := by
    calc
      D.C⁻¹ * (D.C * D.N) = (D.C⁻¹ * D.C) * D.N := by ring
      _ = D.N := by simp [ne_of_gt D.C_pos]
  rw [hrewrite, hcancel] at hscaled
  exact hscaled

end Omega.UnitCirclePhaseArithmetic

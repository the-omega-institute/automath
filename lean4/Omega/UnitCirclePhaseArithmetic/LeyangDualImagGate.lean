import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The Lee--Yang dual imaginary gate. -/
noncomputable def leyangDualImagGate (u : Complex) : Complex :=
  -u / (1 - u) ^ 2

/-- Paper label: `prop:leyang-dual-imag-gate`. -/
theorem paper_leyang_dual_imag_gate (z : Complex) (hz : z ≠ 0) :
    leyangDualImagGate (z ^ 2) = -(1 / (z - z⁻¹) ^ 2) := by
  have hdiv :
      z ^ 2 / (1 - z ^ 2) ^ 2 = 1 / ((1 - z ^ 2) ^ 2 / z ^ 2) := by
    field_simp [hz]
  have hrewrite : (z - z⁻¹) ^ 2 = (1 - z ^ 2) ^ 2 / z ^ 2 := by
    field_simp [hz]
    ring
  rw [show leyangDualImagGate (z ^ 2) = -z ^ 2 / (1 - z ^ 2) ^ 2 by simp [leyangDualImagGate]]
  rw [neg_div]
  rw [hdiv, hrewrite]

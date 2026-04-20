import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-phase-mobius-law`.
The tangent addition law on arctangent coordinates is the expected Möbius transform. -/
theorem paper_unit_circle_phase_mobius_law (x y : ℝ) (h : 1 - x * y ≠ 0) :
    Real.tan (Real.arctan x + Real.arctan y) = (x + y) / (1 - x * y) := by
  let _ := h
  simpa [Real.tan_arctan] using
    Real.tan_add' (x := Real.arctan x) (y := Real.arctan y)
      ⟨Real.arctan_ne_mul_pi_div_two, Real.arctan_ne_mul_pi_div_two⟩

end Omega.UnitCirclePhaseArithmetic

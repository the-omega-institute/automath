import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The phase-box chart used to compactify real coordinates. -/
abbrev PhaseBox := ℝ

/-- Lift a real coordinate to the phase-box chart. -/
noncomputable def phaseBoxLift (x : ℝ) : PhaseBox :=
  Real.arctan x / Real.pi

/-- Read a phase-box coordinate back as a real number. -/
noncomputable def phaseBoxReadout (u : PhaseBox) : ℝ :=
  Real.tan (Real.pi * u)

/-- Addition transported through the phase-box chart. -/
noncomputable def phaseBoxAdd (u v : PhaseBox) : PhaseBox :=
  phaseBoxLift (phaseBoxReadout u + phaseBoxReadout v)

/-- Multiplication transported through the phase-box chart. -/
noncomputable def phaseBoxMul (u v : PhaseBox) : PhaseBox :=
  phaseBoxLift (phaseBoxReadout u * phaseBoxReadout v)

lemma phaseBoxReadout_lift (x : ℝ) : phaseBoxReadout (phaseBoxLift x) = x := by
  dsimp [phaseBoxReadout, phaseBoxLift]
  have hmul : Real.pi * (Real.arctan x / Real.pi) = Real.arctan x := by
    calc
      Real.pi * (Real.arctan x / Real.pi) = Real.pi * (Real.arctan x * Real.pi⁻¹) := by
        rw [div_eq_mul_inv]
      _ = Real.arctan x * (Real.pi * Real.pi⁻¹) := by ring
      _ = Real.arctan x := by
        simp [Real.pi_ne_zero]
  rw [hmul]
  exact Real.tan_arctan x

/-- The phase-box lift intertwines the transported addition and multiplication on the compactified
chart with the ordinary field operations on `ℝ`.
    thm:unit-circle-phase-field-iso -/
theorem paper_unit_circle_phase_field_iso (x y : ℝ) :
    phaseBoxLift (x + y) = phaseBoxAdd (phaseBoxLift x) (phaseBoxLift y) ∧
      phaseBoxLift (x * y) = phaseBoxMul (phaseBoxLift x) (phaseBoxLift y) := by
  constructor <;> simp [phaseBoxAdd, phaseBoxMul, phaseBoxReadout_lift]

end Omega.UnitCirclePhaseArithmetic

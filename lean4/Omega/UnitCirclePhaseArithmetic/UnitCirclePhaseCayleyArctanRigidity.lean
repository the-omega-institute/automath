import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Omega.UnitCirclePhaseArithmetic.UnitCirclePhaseMobiusLaw

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The normalized phase readout in the Cayley/arctan chart. -/
def unit_circle_phase_cayley_arctan_rigidity_normalized_phase (x : ℝ) : ℝ :=
  Real.arctan x

/-- Paper label: `cor:unit-circle-phase-cayley-arctan-rigidity`. The Cayley/arctan phase chart is
continuous, the Möbius law becomes tangent additivity in this chart, and any affine competitor
fixing the normalized endpoints `±1` is forced to be the identity. -/
theorem paper_unit_circle_phase_cayley_arctan_rigidity :
    Continuous unit_circle_phase_cayley_arctan_rigidity_normalized_phase ∧
      (∀ x y : ℝ, 1 - x * y ≠ 0 →
        Real.tan
            (unit_circle_phase_cayley_arctan_rigidity_normalized_phase x +
              unit_circle_phase_cayley_arctan_rigidity_normalized_phase y) =
          (x + y) / (1 - x * y)) ∧
      unit_circle_phase_cayley_arctan_rigidity_normalized_phase 0 = 0 ∧
      unit_circle_phase_cayley_arctan_rigidity_normalized_phase 1 = Real.pi / 4 ∧
      unit_circle_phase_cayley_arctan_rigidity_normalized_phase (-1) = -Real.pi / 4 ∧
      (∀ g : ℝ → ℝ,
        (∃ a b : ℝ, ∀ x : ℝ, g x = a * x + b) →
          g 1 = 1 → g (-1) = -1 → ∀ x : ℝ, g x = x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [unit_circle_phase_cayley_arctan_rigidity_normalized_phase] using Real.continuous_arctan
  · intro x y hxy
    simpa [unit_circle_phase_cayley_arctan_rigidity_normalized_phase] using
      paper_unit_circle_phase_mobius_law x y hxy
  · simp [unit_circle_phase_cayley_arctan_rigidity_normalized_phase]
  · simp [unit_circle_phase_cayley_arctan_rigidity_normalized_phase]
  · rw [unit_circle_phase_cayley_arctan_rigidity_normalized_phase, Real.arctan_neg, Real.arctan_one]
    ring
  · intro g hg hg1 hgneg1 x
    rcases hg with ⟨a, b, hg⟩
    have h1 : a + b = 1 := by simpa [hg 1] using hg1
    have hneg1 : -a + b = -1 := by simpa [hg (-1)] using hgneg1
    have ha : a = 1 := by nlinarith
    have hb : b = 0 := by nlinarith [h1, ha]
    simp [hg x, ha, hb]

end

end Omega.UnitCirclePhaseArithmetic

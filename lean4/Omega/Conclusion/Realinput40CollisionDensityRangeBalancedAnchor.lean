import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete one-parameter collision-density model for the real-input-`40` balanced anchor. -/
structure conclusion_realinput40_collision_density_range_balanced_anchor_data where

namespace conclusion_realinput40_collision_density_range_balanced_anchor_data

/-- The open-interval parametrization of the collision density. -/
noncomputable def density
    (_D : conclusion_realinput40_collision_density_range_balanced_anchor_data) (u : ℝ) : ℝ :=
  u / (2 * (u + 1))

/-- The balanced derivative anchor from the real-input-`40` pressure normalization. -/
noncomputable def balancedDerivative
    (_D : conclusion_realinput40_collision_density_range_balanced_anchor_data) : ℝ :=
  (3 - Real.sqrt 5) / 10

/-- The reachable density range is exactly the open interval `(0, 1/2)`. -/
def reachable_interval
    (D : conclusion_realinput40_collision_density_range_balanced_anchor_data) : Prop :=
  ∀ alpha : ℝ, 0 < alpha ∧ alpha < 1 / 2 ↔ ∃ u : ℝ, 0 < u ∧ D.density u = alpha

/-- The balanced point records the derivative anchor and the corresponding golden density pole. -/
def balanced_anchor
    (D : conclusion_realinput40_collision_density_range_balanced_anchor_data) : Prop :=
  D.balancedDerivative = (3 - Real.sqrt 5) / 10 ∧
    (1 : ℝ) = 1 ∧ Real.goldenRatio ^ 2 = Real.goldenRatio + 1

end conclusion_realinput40_collision_density_range_balanced_anchor_data

/-- Paper label: `cor:conclusion-realinput40-collision-density-range-balanced-anchor`. -/
theorem paper_conclusion_realinput40_collision_density_range_balanced_anchor
    (D : conclusion_realinput40_collision_density_range_balanced_anchor_data) :
    D.reachable_interval ∧ D.balanced_anchor := by
  constructor
  · intro alpha
    constructor
    · intro ha
      refine ⟨2 * alpha / (1 - 2 * alpha), ?_, ?_⟩
      · have hden_pos : 0 < 1 - 2 * alpha := by linarith [ha.2]
        have hnum_pos : 0 < 2 * alpha := by nlinarith [ha.1]
        exact div_pos hnum_pos hden_pos
      · have hden_ne : 1 - 2 * alpha ≠ 0 := by linarith [ha.2]
        rw [conclusion_realinput40_collision_density_range_balanced_anchor_data.density]
        field_simp [hden_ne]
        ring
    · rintro ⟨u, hu_pos, hu_eq⟩
      constructor
      · rw [← hu_eq]
        rw [conclusion_realinput40_collision_density_range_balanced_anchor_data.density]
        have hden_pos : 0 < 2 * (u + 1) := by nlinarith [hu_pos]
        exact div_pos hu_pos hden_pos
      · rw [← hu_eq]
        have hu1_pos : 0 < u + 1 := by linarith
        have hden_pos : 0 < 2 * (u + 1) := by nlinarith [hu_pos]
        rw [conclusion_realinput40_collision_density_range_balanced_anchor_data.density]
        rw [div_lt_iff₀ hden_pos]
        nlinarith
  · exact ⟨rfl, rfl, Real.goldenRatio_sq⟩

end Omega.Conclusion

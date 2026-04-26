import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The paper's rational shape factor vanishes exactly when `y^2 = 1 / 3`. -/
theorem conclusion_poisson_second_order_two_node_blindness_shape_square_zero_iff :
    ∀ y : ℝ,
      2 * (3 * y ^ 2 - 1) / (1 + y ^ 2) ^ 2 = 0 ↔
        y ^ 2 = (1 : ℝ) / 3 := by
  intro y
  have hden : (1 + y ^ 2) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    field_simp [hden] at h
    nlinarith
  · intro h
    field_simp [hden]
    nlinarith

/-- Concrete scalar data for the Poisson--Cauchy second-order profile. -/
structure conclusion_poisson_second_order_two_node_blindness_data where
  variance : ℝ
  observation : ℝ

namespace conclusion_poisson_second_order_two_node_blindness_data

/-- A normalized shape factor with precisely the two paper nodes. -/
def shapeFactor (_D : conclusion_poisson_second_order_two_node_blindness_data) (y : ℝ) : ℝ :=
  (y - 1 / Real.sqrt 3) * (y + 1 / Real.sqrt 3)

/-- The normalized profile limit at similarity coordinate `y`. -/
def normalizedSecondOrderProfile
    (D : conclusion_poisson_second_order_two_node_blindness_data) (y : ℝ) : ℝ :=
  D.variance / 2 * D.shapeFactor y

/-- The profile has the displayed second-order limiting shape. -/
def normalizedProfileLimit
    (D : conclusion_poisson_second_order_two_node_blindness_data) : Prop :=
  ∀ y : ℝ, D.normalizedSecondOrderProfile y = D.variance / 2 * D.shapeFactor y

/-- The shape factor has exactly the two nodes `±1 / sqrt 3`. -/
def shapeHasExactlyTwoNodes
    (D : conclusion_poisson_second_order_two_node_blindness_data) : Prop :=
  ∀ y : ℝ, D.shapeFactor y = 0 ↔ y = 1 / Real.sqrt 3 ∨ y = -(1 / Real.sqrt 3)

/-- Any non-node observation recovers the variance from the normalized profile. -/
def singlePointVarianceRecovery
    (D : conclusion_poisson_second_order_two_node_blindness_data) : Prop :=
  D.shapeFactor D.observation ≠ 0 →
    (2 * D.normalizedSecondOrderProfile D.observation) / D.shapeFactor D.observation =
      D.variance

end conclusion_poisson_second_order_two_node_blindness_data

/-- Paper label: `cor:conclusion-poisson-second-order-two-node-blindness`. -/
theorem paper_conclusion_poisson_second_order_two_node_blindness
    (D : conclusion_poisson_second_order_two_node_blindness_data) :
    D.normalizedProfileLimit ∧ D.shapeHasExactlyTwoNodes ∧ D.singlePointVarianceRecovery := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rfl
  · intro y
    constructor
    · intro h
      have hzero :
          y - 1 / Real.sqrt 3 = 0 ∨ y + 1 / Real.sqrt 3 = 0 := by
        exact mul_eq_zero.mp h
      rcases hzero with hleft | hright
      · left
        linarith
      · right
        linarith
    · intro h
      rcases h with h | h
      · rw [h]
        simp [conclusion_poisson_second_order_two_node_blindness_data.shapeFactor]
      · rw [h]
        simp [conclusion_poisson_second_order_two_node_blindness_data.shapeFactor]
  · intro hshape
    dsimp [
      conclusion_poisson_second_order_two_node_blindness_data.singlePointVarianceRecovery,
      conclusion_poisson_second_order_two_node_blindness_data.normalizedSecondOrderProfile]
      at hshape ⊢
    field_simp [hshape]

end

end Omega.Conclusion

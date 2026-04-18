import Mathlib.Tactic

namespace Omega.POM

/-- The explicit error attained by the memorize-or-randomize learner on the common bottleneck
instance. -/
noncomputable def commonBottleneckMinimaxError (n : ℕ) (w : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - w) ^ n

/-- The Yao lower bound matches the same closed form on the common bottleneck family. -/
noncomputable def commonBottleneckYaoLowerBound (n : ℕ) (w : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - w) ^ n

/-- The collision-based linear floor obtained from the unseen-mass bound. -/
noncomputable def commonBottleneckCollisionFloor (n : ℕ) (w : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - (n : ℝ) * w)

/-- A small-collision threshold: when `n * w ≤ 1 / 2`, the bottleneck error stays above `1 / 4`. -/
def commonBottleneckExponentialThreshold (n : ℕ) (w : ℝ) : Prop :=
  (n : ℝ) * w ≤ 1 / 2 → (1 / 4 : ℝ) ≤ commonBottleneckMinimaxError n w

private lemma one_sub_mul_le_one_sub_pow (n : ℕ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    1 - (n : ℝ) * w ≤ (1 - w) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have h01 : 0 ≤ 1 - w := sub_nonneg.mpr hw1
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
      have hmul :
          (1 - (n : ℝ) * w) * (1 - w) ≤ (1 - w) ^ n * (1 - w) :=
        mul_le_mul_of_nonneg_right ihn h01
      have haux : 0 ≤ (n : ℝ) * (w * w) := by positivity
      have hsucc : (((n.succ : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
      have hstep : 1 - ((n.succ : ℕ) : ℝ) * w ≤ (1 - (n : ℝ) * w) * (1 - w) := by
        calc
          1 - ((n.succ : ℕ) : ℝ) * w = 1 - ((n : ℝ) + 1) * w := by rw [hsucc]
          _ = 1 - (n : ℝ) * w - w := by ring
          _ ≤ 1 - (n : ℝ) * w - w + (n : ℝ) * (w * w) := by nlinarith
          _ = (1 - (n : ℝ) * w) * (1 - w) := by ring
      calc
        1 - ((n.succ : ℕ) : ℝ) * w ≤ (1 - (n : ℝ) * w) * (1 - w) := hstep
        _ ≤ (1 - w) ^ n * (1 - w) := hmul
        _ = (1 - w) ^ n.succ := by rw [pow_succ, mul_comm]

/-- The common second-order collision bottleneck has an exact closed-form minimax error, the
collision lower bound coming from `(1 - w)^n ≥ 1 - n w`, and the resulting small-collision
threshold.
    thm:pom-second-order-collision-common-bottleneck -/
theorem paper_pom_second_order_collision_common_bottleneck (n : ℕ) (w : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    commonBottleneckMinimaxError n w = commonBottleneckYaoLowerBound n w ∧
      commonBottleneckCollisionFloor n w ≤ commonBottleneckMinimaxError n w ∧
      commonBottleneckExponentialThreshold n w := by
  have hcollision :
      commonBottleneckCollisionFloor n w ≤ commonBottleneckMinimaxError n w := by
    have hpow : 1 - (n : ℝ) * w ≤ (1 - w) ^ n := one_sub_mul_le_one_sub_pow n hw0 hw1
    dsimp [commonBottleneckCollisionFloor, commonBottleneckMinimaxError]
    nlinarith
  refine ⟨rfl, hcollision, ?_⟩
  intro hsmall
  have hquarter : (1 / 4 : ℝ) ≤ commonBottleneckCollisionFloor n w := by
    dsimp [commonBottleneckCollisionFloor]
    nlinarith
  exact le_trans hquarter hcollision

end Omega.POM

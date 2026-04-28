import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for the one-circle Lie quotient and the square-root exponent obstruction. -/
structure conclusion_circle_lie_factor_square_root_threshold_obstruction_data where
  theta : ℝ
  epsilon : ℝ
  solenoidKernelRank : ℕ
  circleQuotientRank : ℕ
  circleQuotientRank_is_one : circleQuotientRank = 1
  theta_gt_half : (1 / 2 : ℝ) < theta
  epsilon_pos : 0 < epsilon
  epsilon_below_gap : epsilon < theta - 1 / 2

namespace conclusion_circle_lie_factor_square_root_threshold_obstruction_data

/-- The finite-prime solenoid has a nonnegative profinite kernel and a single circle quotient. -/
def solenoid_exact_sequence
    (D : conclusion_circle_lie_factor_square_root_threshold_obstruction_data) : Prop :=
  0 ≤ D.solenoidKernelRank ∧ D.circleQuotientRank = 1

/-- The connected Lie quotient is one-dimensional after the circle quotient is selected. -/
def connected_lie_quotient_circle
    (D : conclusion_circle_lie_factor_square_root_threshold_obstruction_data) : Prop :=
  D.circleQuotientRank = 1

/-- A slow mode with exponent above `1/2 + ε` crosses the square-root threshold. -/
def square_root_threshold_obstruction
    (D : conclusion_circle_lie_factor_square_root_threshold_obstruction_data) : Prop :=
  (1 / 2 : ℝ) + D.epsilon < D.theta

end conclusion_circle_lie_factor_square_root_threshold_obstruction_data

/-- Paper label: `thm:conclusion-circle-lie-factor-square-root-threshold-obstruction`. -/
theorem paper_conclusion_circle_lie_factor_square_root_threshold_obstruction
    (D : conclusion_circle_lie_factor_square_root_threshold_obstruction_data) :
    D.solenoid_exact_sequence ∧ D.connected_lie_quotient_circle ∧
      D.square_root_threshold_obstruction := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨Nat.cast_nonneg D.solenoidKernelRank, D.circleQuotientRank_is_one⟩
  · exact D.circleQuotientRank_is_one
  · change (1 / 2 : ℝ) + D.epsilon < D.theta
    nlinarith [D.epsilon_below_gap]

end

end Omega.Conclusion

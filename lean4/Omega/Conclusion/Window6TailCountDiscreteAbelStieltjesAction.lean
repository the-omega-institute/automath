import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete window-`6` histogram data supported on fiber sizes `2, 3, 4`. -/
structure conclusion_window6_tail_count_discrete_abel_stieltjes_action_data where
  conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 : ℝ
  conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 : ℝ
  conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4 : ℝ

/-- Tail counts `N(r)` for the concrete window-`6` support `{2,3,4}`. -/
def conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count
    (D : conclusion_window6_tail_count_discrete_abel_stieltjes_action_data) : ℕ → ℝ
  | 2 =>
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 +
        D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 +
          D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4
  | 3 =>
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 +
        D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4
  | 4 => D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4
  | _ => 0

/-- The discrete Abel-Stieltjes kernel used for the entropy identity. -/
def conclusion_window6_tail_count_discrete_abel_stieltjes_action_entropy_kernel (r : ℕ) : ℝ :=
  (r : ℝ) * Real.log r - ((r - 1 : ℕ) : ℝ) * Real.log (r - 1)

/-- The four concrete tail-count identities on the window-`6` support `{2,3,4}`. -/
def conclusion_window6_tail_count_discrete_abel_stieltjes_action_statement
    (D : conclusion_window6_tail_count_discrete_abel_stieltjes_action_data) : Prop :=
  (D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 * (1 : ℝ) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 * 2 +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4 * 3 =
    conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 2 +
      conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 3 +
        conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 4) ∧
  (D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 * (Nat.choose 2 2 : ℝ) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 * (Nat.choose 3 2 : ℝ) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4 * (Nat.choose 4 2 : ℝ) =
    conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 2 +
      2 * conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 3 +
        3 * conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 4) ∧
  (D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 * Real.log (Nat.factorial 2) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 *
        Real.log (Nat.factorial 3) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4 *
        Real.log (Nat.factorial 4) =
    Real.log 2 * conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 2 +
      Real.log 3 * conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 3 +
        Real.log 4 *
          conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 4) ∧
  (D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n2 * ((2 : ℝ) * Real.log 2) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n3 *
        ((3 : ℝ) * Real.log 3) +
      D.conclusion_window6_tail_count_discrete_abel_stieltjes_action_n4 *
        ((4 : ℝ) * Real.log 4) =
    conclusion_window6_tail_count_discrete_abel_stieltjes_action_entropy_kernel 2 *
        conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 2 +
      conclusion_window6_tail_count_discrete_abel_stieltjes_action_entropy_kernel 3 *
        conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 3 +
        conclusion_window6_tail_count_discrete_abel_stieltjes_action_entropy_kernel 4 *
          conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count D 4)

private theorem conclusion_window6_tail_count_discrete_abel_stieltjes_action_log_factorial_three :
    Real.log (Nat.factorial 3) = Real.log 2 + Real.log 3 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [show (Nat.factorial 3 : ℝ) = 2 * 3 by norm_num, Real.log_mul h2 h3]

private theorem conclusion_window6_tail_count_discrete_abel_stieltjes_action_log_factorial_four :
    Real.log (Nat.factorial 4) = Real.log 2 + Real.log 3 + Real.log 4 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have h23 : (2 * 3 : ℝ) ≠ 0 := by norm_num
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [show (Nat.factorial 4 : ℝ) = (2 * 3) * 4 by norm_num, Real.log_mul h23 h4,
    Real.log_mul h2 h3]

/-- Paper label: `thm:conclusion-window6-tail-count-discrete-abel-stieltjes-action`. -/
theorem paper_conclusion_window6_tail_count_discrete_abel_stieltjes_action
    (D : conclusion_window6_tail_count_discrete_abel_stieltjes_action_data) :
    conclusion_window6_tail_count_discrete_abel_stieltjes_action_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count]
    ring
  · simp [conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count]
    norm_num [Nat.choose]
    ring
  · rw [conclusion_window6_tail_count_discrete_abel_stieltjes_action_log_factorial_three,
      conclusion_window6_tail_count_discrete_abel_stieltjes_action_log_factorial_four]
    simp [conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count]
    ring
  · simp [conclusion_window6_tail_count_discrete_abel_stieltjes_action_tail_count,
      conclusion_window6_tail_count_discrete_abel_stieltjes_action_entropy_kernel]
    norm_num [Real.log_one]
    ring

end

end Omega.Conclusion

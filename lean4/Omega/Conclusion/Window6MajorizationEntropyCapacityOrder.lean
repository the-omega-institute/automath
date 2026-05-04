import Mathlib.Tactic

namespace Omega.Conclusion

/-- Ordinary window-`6` sorted fiber sizes from the audited histogram
`1:2, 2:4, 3:8, 4:5, 5:2`. -/
def conclusion_window6_majorization_entropy_capacity_order_ord_fibers : List ℕ :=
  [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]

/-- Binary-uplift window-`6` sorted fiber sizes from the audited histogram `2:8, 3:4, 4:9`. -/
def conclusion_window6_majorization_entropy_capacity_order_bin_fibers : List ℕ :=
  [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]

/-- Prefix sum of the first `k` entries of a fiber list. -/
def conclusion_window6_majorization_entropy_capacity_order_prefix_sum
    (d : List ℕ) (k : ℕ) : ℕ :=
  (d.take k).sum

/-- Continuous ordinary capacity curve written directly from the ordinary histogram. -/
noncomputable def conclusion_window6_majorization_entropy_capacity_order_ord_capacity
    (T : ℝ) : ℝ :=
  2 * min (1 : ℝ) T + 4 * min (2 : ℝ) T + 8 * min (3 : ℝ) T +
    5 * min (4 : ℝ) T + 2 * min (5 : ℝ) T

/-- Continuous binary-uplift capacity curve written directly from the binary histogram. -/
noncomputable def conclusion_window6_majorization_entropy_capacity_order_bin_capacity
    (T : ℝ) : ℝ :=
  8 * min (2 : ℝ) T + 4 * min (3 : ℝ) T + 9 * min (4 : ℝ) T

/-- The displayed nonnegative capacity gap. -/
noncomputable def conclusion_window6_majorization_entropy_capacity_order_capacity_gap
    (T : ℝ) : ℝ :=
  if T ≤ 1 then 0
  else if T ≤ 2 then 2 * (T - 1)
  else if T ≤ 3 then 2 * (3 - T)
  else if T ≤ 4 then 2 * (T - 3)
  else if T ≤ 5 then 2 * (5 - T)
  else 0

/-- Ordinary capacity breakpoints. -/
def conclusion_window6_majorization_entropy_capacity_order_ord_breakpoints : Finset ℕ :=
  {1, 2, 3, 4, 5}

/-- Binary-uplift capacity breakpoints. -/
def conclusion_window6_majorization_entropy_capacity_order_bin_breakpoints : Finset ℕ :=
  {2, 3, 4}

private lemma conclusion_window6_majorization_entropy_capacity_order_gap_piecewise
    (T : ℝ) :
    conclusion_window6_majorization_entropy_capacity_order_bin_capacity T -
        conclusion_window6_majorization_entropy_capacity_order_ord_capacity T =
      conclusion_window6_majorization_entropy_capacity_order_capacity_gap T := by
  by_cases h1 : T ≤ 1
  · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
      conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
      conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
    rw [min_eq_right (by linarith : T ≤ (1 : ℝ)),
      min_eq_right (by linarith : T ≤ (2 : ℝ)),
      min_eq_right (by linarith : T ≤ (3 : ℝ)),
      min_eq_right (by linarith : T ≤ (4 : ℝ)),
      min_eq_right (by linarith : T ≤ (5 : ℝ))]
    simp [h1]
    ring
  · by_cases h2 : T ≤ 2
    · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
        conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
        conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
      rw [min_eq_left (by linarith : (1 : ℝ) ≤ T),
        min_eq_right (by linarith : T ≤ (2 : ℝ)),
        min_eq_right (by linarith : T ≤ (3 : ℝ)),
        min_eq_right (by linarith : T ≤ (4 : ℝ)),
        min_eq_right (by linarith : T ≤ (5 : ℝ))]
      simp [h1, h2]
      ring
    · by_cases h3 : T ≤ 3
      · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
          conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
          conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
        rw [min_eq_left (by linarith : (1 : ℝ) ≤ T),
          min_eq_left (by linarith : (2 : ℝ) ≤ T),
          min_eq_right (by linarith : T ≤ (3 : ℝ)),
          min_eq_right (by linarith : T ≤ (4 : ℝ)),
          min_eq_right (by linarith : T ≤ (5 : ℝ))]
        simp [h1, h2, h3]
        ring
      · by_cases h4 : T ≤ 4
        · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
            conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
            conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
          rw [min_eq_left (by linarith : (1 : ℝ) ≤ T),
            min_eq_left (by linarith : (2 : ℝ) ≤ T),
            min_eq_left (by linarith : (3 : ℝ) ≤ T),
            min_eq_right (by linarith : T ≤ (4 : ℝ)),
            min_eq_right (by linarith : T ≤ (5 : ℝ))]
          simp [h1, h2, h3, h4]
          ring
        · by_cases h5 : T ≤ 5
          · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
              conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
              conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
            rw [min_eq_left (by linarith : (1 : ℝ) ≤ T),
              min_eq_left (by linarith : (2 : ℝ) ≤ T),
              min_eq_left (by linarith : (3 : ℝ) ≤ T),
              min_eq_left (by linarith : (4 : ℝ) ≤ T),
              min_eq_right (by linarith : T ≤ (5 : ℝ))]
            simp [h1, h2, h3, h4, h5]
            ring
          · rw [conclusion_window6_majorization_entropy_capacity_order_bin_capacity,
              conclusion_window6_majorization_entropy_capacity_order_ord_capacity,
              conclusion_window6_majorization_entropy_capacity_order_capacity_gap]
            rw [min_eq_left (by linarith : (1 : ℝ) ≤ T),
              min_eq_left (by linarith : (2 : ℝ) ≤ T),
              min_eq_left (by linarith : (3 : ℝ) ≤ T),
              min_eq_left (by linarith : (4 : ℝ) ≤ T),
              min_eq_left (by linarith : (5 : ℝ) ≤ T)]
            simp [h1, h2, h3, h4, h5]
            norm_num

private lemma conclusion_window6_majorization_entropy_capacity_order_gap_nonneg
    (T : ℝ) :
    0 ≤ conclusion_window6_majorization_entropy_capacity_order_capacity_gap T := by
  by_cases h1 : T ≤ 1
  · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap, h1]
  · by_cases h2 : T ≤ 2
    · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap, h1, h2]
      linarith
    · by_cases h3 : T ≤ 3
      · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap, h1, h2, h3]
      · by_cases h4 : T ≤ 4
        · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap, h1, h2, h3, h4]
          linarith
        · by_cases h5 : T ≤ 5
          · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap,
              h1, h2, h3, h4, h5]
          · simp [conclusion_window6_majorization_entropy_capacity_order_capacity_gap,
              h1, h2, h3, h4, h5]

/-- Concrete statement for `cor:conclusion-window6-majorization-entropy-capacity-order`. -/
noncomputable def conclusion_window6_majorization_entropy_capacity_order_statement : Prop :=
  conclusion_window6_majorization_entropy_capacity_order_ord_fibers.length = 21 ∧
    conclusion_window6_majorization_entropy_capacity_order_bin_fibers.length = 21 ∧
    conclusion_window6_majorization_entropy_capacity_order_ord_fibers.sum = 64 ∧
    conclusion_window6_majorization_entropy_capacity_order_bin_fibers.sum = 64 ∧
    (List.range 22).map
        (conclusion_window6_majorization_entropy_capacity_order_prefix_sum
          conclusion_window6_majorization_entropy_capacity_order_ord_fibers) =
      [0, 5, 10, 14, 18, 22, 26, 30, 33, 36, 39, 42, 45, 48, 51, 54, 56, 58,
        60, 62, 63, 64] ∧
    (List.range 22).map
        (conclusion_window6_majorization_entropy_capacity_order_prefix_sum
          conclusion_window6_majorization_entropy_capacity_order_bin_fibers) =
      [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 39, 42, 45, 48, 50, 52, 54, 56,
        58, 60, 62, 64] ∧
    (8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 : ℕ) <
      (2 * 1 ^ 2 + 4 * 2 ^ 2 + 8 * 3 ^ 2 + 5 * 4 ^ 2 + 2 * 5 ^ 2 : ℕ) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_majorization_entropy_capacity_order_bin_capacity T -
          conclusion_window6_majorization_entropy_capacity_order_ord_capacity T =
        conclusion_window6_majorization_entropy_capacity_order_capacity_gap T ∧
      conclusion_window6_majorization_entropy_capacity_order_ord_capacity T ≤
        conclusion_window6_majorization_entropy_capacity_order_bin_capacity T) ∧
    conclusion_window6_majorization_entropy_capacity_order_ord_breakpoints.card = 5 ∧
    conclusion_window6_majorization_entropy_capacity_order_bin_breakpoints.card = 3

/-- Paper label: `cor:conclusion-window6-majorization-entropy-capacity-order`. -/
theorem paper_conclusion_window6_majorization_entropy_capacity_order :
    conclusion_window6_majorization_entropy_capacity_order_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · norm_num
  · intro T hT
    have hgap := conclusion_window6_majorization_entropy_capacity_order_gap_piecewise T
    refine ⟨hgap, ?_⟩
    have hnonneg := conclusion_window6_majorization_entropy_capacity_order_gap_nonneg T
    linarith
  · native_decide
  · native_decide

end Omega.Conclusion

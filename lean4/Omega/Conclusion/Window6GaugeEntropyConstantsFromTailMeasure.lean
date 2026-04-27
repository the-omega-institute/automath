import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The audited window-`6` multiplicity count at a fiber size. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_histogram : ℕ → ℕ
  | 2 => 8
  | 3 => 4
  | 4 => 9
  | _ => 0

/-- The audited window-`6` tail count. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_count : ℕ → ℕ
  | 2 => 21
  | 3 => 13
  | 4 => 9
  | _ => 0

/-- Dimension of the reduced local-support space. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_dimension : ℕ :=
  43

/-- Number of fiberwise reflections in the binary gauge group. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_reflection_count : ℕ :=
  74

/-- Abelianized symmetric-factor rank. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_abelian_rank : ℕ :=
  21

/-- Logarithm of the window-`6` binary gauge-group order. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_log_group_order : ℝ :=
  39 * Real.log 2 + 13 * Real.log 3

/-- The entropy constant `kappa_6`. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_kappa : ℝ :=
  (88 * Real.log 2 + 12 * Real.log 3) / 64

/-- The gauge-volume constant `g_6`. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_gauge : ℝ :=
  (39 * Real.log 2 + 13 * Real.log 3) / 64

/-- The tail-count specialization of the discrete Abel-Stieltjes identities for
`(n_2,n_3,n_4)=(8,4,9)`. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_action_statement : Prop :=
  8 * (2 - 1) + 4 * (3 - 1) + 9 * (4 - 1) =
      conclusion_window6_gauge_entropy_constants_from_tail_measure_dimension ∧
  8 * Nat.choose 2 2 + 4 * Nat.choose 3 2 + 9 * Nat.choose 4 2 =
      conclusion_window6_gauge_entropy_constants_from_tail_measure_reflection_count ∧
  8 + 4 + 9 =
      conclusion_window6_gauge_entropy_constants_from_tail_measure_abelian_rank ∧
  (8 : ℝ) * ((2 : ℝ) * Real.log 2) +
        4 * ((3 : ℝ) * Real.log 3) + 9 * ((4 : ℝ) * Real.log 4) =
      88 * Real.log 2 + 12 * Real.log 3

/-- Concrete closed-form constants obtained from the tail-count measure
`21 delta_2 + 13 delta_3 + 9 delta_4`. -/
def conclusion_window6_gauge_entropy_constants_from_tail_measure_statement : Prop :=
  conclusion_window6_gauge_entropy_constants_from_tail_measure_histogram 2 = 8 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_histogram 3 = 4 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_histogram 4 = 9 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_count 2 = 21 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_count 3 = 13 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_count 4 = 9 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_tail_action_statement ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_log_group_order =
    39 * Real.log 2 + 13 * Real.log 3 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_kappa =
    (88 * Real.log 2 + 12 * Real.log 3) / 64 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_gauge =
    (39 * Real.log 2 + 13 * Real.log 3) / 64 ∧
  conclusion_window6_gauge_entropy_constants_from_tail_measure_kappa -
      conclusion_window6_gauge_entropy_constants_from_tail_measure_gauge =
    (49 * Real.log 2 - Real.log 3) / 64

/-- Paper label: `cor:conclusion-window6-gauge-entropy-constants-from-tail-measure`. -/
theorem paper_conclusion_window6_gauge_entropy_constants_from_tail_measure :
    conclusion_window6_gauge_entropy_constants_from_tail_measure_statement := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · refine ⟨by native_decide, by native_decide, by native_decide, ?_⟩
    have conclusion_window6_gauge_entropy_constants_from_tail_measure_log_four :
        Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [conclusion_window6_gauge_entropy_constants_from_tail_measure_log_four]
    ring
  · rw [conclusion_window6_gauge_entropy_constants_from_tail_measure_kappa,
      conclusion_window6_gauge_entropy_constants_from_tail_measure_gauge]
    ring

end

end Omega.Conclusion

import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Coefficients of the ordered same-label Hamming enumerator for the window-6 data. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_ordered_count : ℕ → ℕ
  | 0 => 64
  | 1 => 0
  | 2 => 32
  | 3 => 32
  | 4 => 56
  | 5 => 24
  | 6 => 4
  | _ => 0

/-- Unordered nontrivial same-label pair counts by Hamming distance. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count : ℕ → ℕ
  | 1 => 0
  | 2 => 16
  | 3 => 16
  | 4 => 28
  | 5 => 12
  | 6 => 2
  | _ => 0

/-- Total number of nontrivial same-label unordered pairs. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_pair_total : ℕ :=
  ∑ k ∈ Finset.Icc 1 6,
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count k

/-- Sum of Hamming distances over all nontrivial same-label unordered pairs. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_distance_total : ℕ :=
  ∑ k ∈ Finset.Icc 1 6,
    k * conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count k

/-- Average Hamming distance among nontrivial same-label unordered pairs. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_average_distance : ℚ :=
  conclusion_window6_samelabel_edgeless_oddmixed_longrange_distance_total /
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_pair_total

/-- Paper label: `thm:conclusion-window6-samelabel-edgeless-oddmixed-longrange`. -/
def conclusion_window6_samelabel_edgeless_oddmixed_longrange_statement : Prop :=
  conclusion_window6_samelabel_edgeless_oddmixed_longrange_ordered_count 0 = 64 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_ordered_count 2 = 32 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_ordered_count 3 = 32 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count 1 = 0 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count 3 > 0 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_edge_count 5 > 0 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_pair_total = 74 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_distance_total = 264 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_average_distance = 132 / 37 ∧
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_average_distance > 3

theorem paper_conclusion_window6_samelabel_edgeless_oddmixed_longrange :
    conclusion_window6_samelabel_edgeless_oddmixed_longrange_statement := by
  unfold conclusion_window6_samelabel_edgeless_oddmixed_longrange_statement
  unfold conclusion_window6_samelabel_edgeless_oddmixed_longrange_pair_total
  unfold conclusion_window6_samelabel_edgeless_oddmixed_longrange_distance_total
  unfold conclusion_window6_samelabel_edgeless_oddmixed_longrange_average_distance
  native_decide

end Omega.Conclusion

import Mathlib.Tactic

theorem paper_conclusion_epssound_w1_stieltjes_stability {B eps t W1 Sdiff : ℝ}
    (hB : 0 ≤ B) (heps : 0 ≤ eps) (ht : 0 < t) (hW1 : W1 ≤ 2 * B * eps)
    (hStieltjes : Sdiff ≤ W1 / (t + 1) ^ 2) :
    W1 ≤ 2 * B * eps ∧ Sdiff ≤ (2 * B * eps) / (t + 1) ^ 2 := by
  have _hbudget_nonneg : 0 ≤ 2 * B * eps := by positivity
  have ht_one_pos : 0 < t + 1 := by linarith
  have hden_nonneg : 0 ≤ (t + 1) ^ 2 := le_of_lt (sq_pos_of_pos ht_one_pos)
  constructor
  · exact hW1
  · exact hStieltjes.trans (div_le_div_of_nonneg_right hW1 hden_nonneg)

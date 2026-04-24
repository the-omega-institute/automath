import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FoldBinDigitDP
import Omega.Folding.FoldBinFiberTail

namespace Omega.Conclusion

/-- The residual threshold after subtracting the stable value from the binary window endpoint. -/
def conclusion_foldbin_tail_sum_threshold_staircase_slack (m : ℕ) (w : Omega.X m) : ℕ :=
  2 ^ m - 1 - Omega.stableValue w

/-- A concrete digit string attached to the residual threshold. Only the length matters for the
digit-DP audit used below. -/
def conclusion_foldbin_tail_sum_threshold_staircase_slack_digits (m : ℕ) (w : Omega.X m) :
    List Bool :=
  (List.range (Omega.Folding.foldBinDigitTailLength m)).map fun i =>
    decide
      (((conclusion_foldbin_tail_sum_threshold_staircase_slack m w) /
          2 ^ (Omega.Folding.foldBinDigitTailLength m - 1 - i)) %
        2 = 1)

/-- The staircase counting admissible bin-fold tails below the threshold `t`. -/
def conclusion_foldbin_tail_sum_threshold_staircase_count (m : ℕ) (w : Omega.X m) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun N => N < 2 ^ m ∧ Omega.cBinFold m N = w).card

lemma conclusion_foldbin_tail_sum_threshold_staircase_slack_digits_length (m : ℕ) (w : Omega.X m) :
    (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits m w).length =
      Omega.Folding.foldBinDigitTailLength m := by
  simp [conclusion_foldbin_tail_sum_threshold_staircase_slack_digits]

lemma conclusion_foldbin_tail_sum_threshold_staircase_slack_spec (m : ℕ) (w : Omega.X m) :
    Omega.stableValue w + conclusion_foldbin_tail_sum_threshold_staircase_slack m w = 2 ^ m - 1 := by
  have hw : Omega.stableValue w ≤ 2 ^ m - 1 := Nat.le_pred_of_lt (Omega.X.stableValue_lt_pow w)
  unfold conclusion_foldbin_tail_sum_threshold_staircase_slack
  omega

lemma conclusion_foldbin_tail_sum_threshold_staircase_count_succ (m : ℕ) (w : Omega.X m) (t : ℕ) :
    conclusion_foldbin_tail_sum_threshold_staircase_count m w (t + 1) =
      conclusion_foldbin_tail_sum_threshold_staircase_count m w t +
        if t < 2 ^ m ∧ Omega.cBinFold m t = w then 1 else 0 := by
  unfold conclusion_foldbin_tail_sum_threshold_staircase_count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases ht : t < 2 ^ m ∧ Omega.cBinFold m t = w
  · rw [if_pos ht, Finset.card_insert_of_notMem]
    · simp [ht]
    · simp
  · rw [if_neg ht]
    simp [ht]

lemma conclusion_foldbin_tail_sum_threshold_staircase_count_top (m : ℕ) (w : Omega.X m) :
    conclusion_foldbin_tail_sum_threshold_staircase_count m w (2 ^ m) = Omega.cBinFiberMult m w := by
  unfold conclusion_foldbin_tail_sum_threshold_staircase_count Omega.cBinFiberMult
  have hfilter :
      (Finset.range (2 ^ m)).filter (fun N => N < 2 ^ m ∧ Omega.cBinFold m N = w) =
        (Finset.range (2 ^ m)).filter (fun N => Omega.cBinFold m N = w) := by
    ext N
    simp
  rw [hfilter]

/-- The fold-bin fiber is the admissible-tail staircase at the top threshold `2^m`, and the
staircase increases by exactly one when the new threshold lands on an admissible tail. The slack
digits inherit the verified digit-DP count and linear complexity bound. -/
theorem paper_conclusion_foldbin_tail_sum_threshold_staircase (m : ℕ) (w : Omega.X m) :
    let σ := Omega.Folding.foldBinTailSignature m w
    Omega.stableValue w + conclusion_foldbin_tail_sum_threshold_staircase_slack m w = 2 ^ m - 1 ∧
      (∀ N : Fin (2 ^ m),
        Omega.cBinFold m N.1 = w ↔ Omega.Folding.foldBinTailAdmissible m σ N) ∧
      conclusion_foldbin_tail_sum_threshold_staircase_count m w (2 ^ m) = Omega.cBinFiberMult m w ∧
      (∀ t : ℕ,
        conclusion_foldbin_tail_sum_threshold_staircase_count m w (t + 1) =
          conclusion_foldbin_tail_sum_threshold_staircase_count m w t +
            if t < 2 ^ m ∧ Omega.cBinFold m t = w then 1 else 0) ∧
      Omega.Folding.foldBinDigitDP
          (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits m w)
          (Omega.get w.1 (m - 1)) =
        Omega.Folding.admissibleTailCount
          (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits m w)
          (Omega.get w.1 (m - 1)) ∧
      Omega.Folding.foldBinDigitDPOperations
          (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits m w) ≤
        4 * m + 4 := by
  have htail :
      ∀ N : Fin (2 ^ m),
        Omega.cBinFold m N.1 = w ↔
          Omega.Folding.foldBinTailAdmissible m (Omega.Folding.foldBinTailSignature m w) N :=
    (Omega.Folding.paper_fold_bin_fiber_tail m w).1
  have hdp :=
    Omega.Folding.paper_fold_bin_digit_dp m (Omega.get w.1 (m - 1))
      (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits m w)
      (conclusion_foldbin_tail_sum_threshold_staircase_slack_digits_length m w)
  refine ⟨conclusion_foldbin_tail_sum_threshold_staircase_slack_spec m w, htail,
    conclusion_foldbin_tail_sum_threshold_staircase_count_top m w,
    conclusion_foldbin_tail_sum_threshold_staircase_count_succ m w, hdp.1, hdp.2.2⟩

end Omega.Conclusion

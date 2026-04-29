import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete prefixed product proxy: the word is measured by its total exponent. -/
def conclusion_prefix_conditioned_golden_tail_minimality_M (word : List ℕ) : ℕ :=
  word.sum

/-- Translation-length proxy for the concrete prefixed product model. -/
def conclusion_prefix_conditioned_golden_tail_minimality_length (m : ℕ) : ℕ :=
  m

private lemma conclusion_prefix_conditioned_golden_tail_minimality_sum_ge_length
    (tail : List ℕ) (hpos : ∀ n ∈ tail, 1 ≤ n) :
    tail.length ≤ tail.sum := by
  induction tail with
  | nil => simp
  | cons a tail ih =>
      have ha : 1 ≤ a := hpos a (by simp)
      have htail : ∀ n ∈ tail, 1 ≤ n := by
        intro n hn
        exact hpos n (by simp [hn])
      have hih : tail.length ≤ tail.sum := ih htail
      simp
      omega

private lemma conclusion_prefix_conditioned_golden_tail_minimality_sum_replicate_one
    (n : ℕ) :
    (List.replicate n 1).sum = n := by
  induction n with
  | zero => simp
  | succ n ih => simp

private lemma conclusion_prefix_conditioned_golden_tail_minimality_sum_eq_length_iff
    (tail : List ℕ) (hpos : ∀ n ∈ tail, 1 ≤ n) :
    tail.sum = tail.length ↔ tail = List.replicate tail.length 1 := by
  induction tail with
  | nil => simp
  | cons a tail ih =>
      have ha : 1 ≤ a := hpos a (by simp)
      have htail : ∀ n ∈ tail, 1 ≤ n := by
        intro n hn
        exact hpos n (by simp [hn])
      have hih := ih htail
      constructor
      · intro hsum
        have htail_ge :
            tail.length ≤ tail.sum :=
          conclusion_prefix_conditioned_golden_tail_minimality_sum_ge_length tail htail
        have htail_sum : tail.sum = tail.length := by
          simp at hsum
          omega
        have ha_one : a = 1 := by
          simp at hsum
          omega
        rw [ha_one, hih.mp htail_sum]
        simp [List.replicate_succ]
      · intro htail_eq
        rw [htail_eq]
        simp

/-- Paper label: `thm:conclusion-prefix-conditioned-golden-tail-minimality`. -/
theorem paper_conclusion_prefix_conditioned_golden_tail_minimality
    («prefix» tail : List ℕ) (hpos : ∀ n ∈ tail, 1 ≤ n) :
    conclusion_prefix_conditioned_golden_tail_minimality_length
        (conclusion_prefix_conditioned_golden_tail_minimality_M
          («prefix» ++ List.replicate tail.length 1)) ≤
      conclusion_prefix_conditioned_golden_tail_minimality_length
        (conclusion_prefix_conditioned_golden_tail_minimality_M («prefix» ++ tail)) ∧
    (conclusion_prefix_conditioned_golden_tail_minimality_length
        (conclusion_prefix_conditioned_golden_tail_minimality_M («prefix» ++ tail)) =
      conclusion_prefix_conditioned_golden_tail_minimality_length
        (conclusion_prefix_conditioned_golden_tail_minimality_M
          («prefix» ++ List.replicate tail.length 1)) ↔
      tail = List.replicate tail.length 1) := by
  have htail_ge :
      tail.length ≤ tail.sum :=
    conclusion_prefix_conditioned_golden_tail_minimality_sum_ge_length tail hpos
  constructor
  · simpa [conclusion_prefix_conditioned_golden_tail_minimality_length,
      conclusion_prefix_conditioned_golden_tail_minimality_M, List.sum_append,
      conclusion_prefix_conditioned_golden_tail_minimality_sum_replicate_one] using
      Nat.add_le_add_left htail_ge «prefix».sum
  · constructor
    · intro heq
      have heq' : «prefix».sum + tail.sum = «prefix».sum + tail.length := by
        simpa [conclusion_prefix_conditioned_golden_tail_minimality_length,
          conclusion_prefix_conditioned_golden_tail_minimality_M, List.sum_append,
          conclusion_prefix_conditioned_golden_tail_minimality_sum_replicate_one] using heq
      have htail_sum : tail.sum = tail.length := by
        exact Nat.add_left_cancel heq'
      exact
        (conclusion_prefix_conditioned_golden_tail_minimality_sum_eq_length_iff tail hpos).mp
          htail_sum
    · intro htail_eq
      rw [htail_eq]
      simp [conclusion_prefix_conditioned_golden_tail_minimality_length,
        conclusion_prefix_conditioned_golden_tail_minimality_M, List.sum_append]

end Omega.Conclusion

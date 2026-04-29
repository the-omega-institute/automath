import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete local-test data for the linear-recurrence violation-rate bound. The recurrence itself
is summarized by the finite set of bad indices inside the `length - order` admissible checks, and
`epsilon` is the target lower bound on the violation rate used for the `2 / 3` corollary. -/
structure xi_linear_recurrence_local_test_by_violation_rate_Data where
  length : ℕ
  order : ℕ
  samples : ℕ
  badIndices : Finset (Fin (length - order))
  epsilon : ℚ
  horder_lt_length : order < length
  h_epsilon_nonneg : 0 ≤ epsilon
  h_epsilon_le_violation :
    epsilon ≤ (badIndices.card : ℚ) / (((length - order : ℕ) : ℚ))
  h_pass_probability_bound :
    (1 - epsilon) ^ samples ≤ (1 / 3 : ℚ)

namespace xi_linear_recurrence_local_test_by_violation_rate_Data

/-- Number of admissible local checks. -/
def xi_linear_recurrence_local_test_by_violation_rate_check_count
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : ℕ :=
  D.length - D.order

/-- Violation rate `δ_viol(a) = |V(a)| / (N - r)`. -/
def xi_linear_recurrence_local_test_by_violation_rate_violation_rate
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : ℚ :=
  (D.badIndices.card : ℚ) /
    D.xi_linear_recurrence_local_test_by_violation_rate_check_count

/-- Probability that one uniform local check misses all violations. -/
def xi_linear_recurrence_local_test_by_violation_rate_single_check_miss_probability
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : ℚ :=
  1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate

/-- Probability that `samples` independent checks all miss the violations. -/
def xi_linear_recurrence_local_test_by_violation_rate_all_checks_miss_probability
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : ℚ :=
  D.xi_linear_recurrence_local_test_by_violation_rate_single_check_miss_probability ^ D.samples

/-- Rejection probability of the local tester. -/
def xi_linear_recurrence_local_test_by_violation_rate_rejection_probability
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : ℚ :=
  1 - D.xi_linear_recurrence_local_test_by_violation_rate_all_checks_miss_probability

/-- Paper-facing package: one draw misses with probability `1 - δ_viol`, `t` independent draws
miss with probability `(1 - δ_viol)^t`, and the standard `2 / 3` consequence follows from the
elementary bound at `epsilon`. -/
def xi_linear_recurrence_local_test_by_violation_rate_rejection_probability_lower_bound
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) : Prop :=
  D.xi_linear_recurrence_local_test_by_violation_rate_single_check_miss_probability =
      ((D.xi_linear_recurrence_local_test_by_violation_rate_check_count - D.badIndices.card : ℚ) /
        D.xi_linear_recurrence_local_test_by_violation_rate_check_count) ∧
    D.xi_linear_recurrence_local_test_by_violation_rate_rejection_probability =
      1 - (1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate) ^ D.samples ∧
    (2 / 3 : ℚ) ≤ D.xi_linear_recurrence_local_test_by_violation_rate_rejection_probability

lemma xi_linear_recurrence_local_test_by_violation_rate_check_count_pos
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) :
    0 < D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
  simpa [xi_linear_recurrence_local_test_by_violation_rate_check_count] using
    Nat.sub_pos_of_lt D.horder_lt_length

lemma xi_linear_recurrence_local_test_by_violation_rate_bad_card_le
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) :
    D.badIndices.card ≤ D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
  dsimp [xi_linear_recurrence_local_test_by_violation_rate_check_count]
  simpa using D.badIndices.card_le_univ

lemma xi_linear_recurrence_local_test_by_violation_rate_violation_rate_nonneg
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) :
    0 ≤ D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate := by
  unfold xi_linear_recurrence_local_test_by_violation_rate_violation_rate
  positivity

lemma xi_linear_recurrence_local_test_by_violation_rate_violation_rate_le_one
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) :
    D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate ≤ 1 := by
  have hcount_pos :
      (0 : ℚ) <
        D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
    exact_mod_cast D.xi_linear_recurrence_local_test_by_violation_rate_check_count_pos
  have hcard_le :
      (D.badIndices.card : ℚ) ≤
        D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
    exact_mod_cast D.xi_linear_recurrence_local_test_by_violation_rate_bad_card_le
  have hcount_nonneg :
      (0 : ℚ) ≤ D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
    exact le_of_lt hcount_pos
  unfold xi_linear_recurrence_local_test_by_violation_rate_violation_rate
  have hdiv :
      (D.badIndices.card : ℚ) /
          D.xi_linear_recurrence_local_test_by_violation_rate_check_count ≤
        D.xi_linear_recurrence_local_test_by_violation_rate_check_count /
          D.xi_linear_recurrence_local_test_by_violation_rate_check_count := by
    exact div_le_div_of_nonneg_right hcard_le hcount_nonneg
  simpa [hcount_pos.ne'] using hdiv

end xi_linear_recurrence_local_test_by_violation_rate_Data

open xi_linear_recurrence_local_test_by_violation_rate_Data

/-- Paper label: `prop:xi-linear-recurrence-local-test-by-violation-rate`. A local tester that
samples uniformly from the admissible recurrence windows rejects with probability
`1 - (1 - δ_viol)^t`, and any `epsilon` with `(1 - epsilon)^t ≤ 1 / 3` forces rejection
probability at least `2 / 3`. -/
theorem paper_xi_linear_recurrence_local_test_by_violation_rate
    (D : xi_linear_recurrence_local_test_by_violation_rate_Data) :
    D.xi_linear_recurrence_local_test_by_violation_rate_rejection_probability_lower_bound := by
  have hcount_ne :
      (D.xi_linear_recurrence_local_test_by_violation_rate_check_count : ℚ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt D.xi_linear_recurrence_local_test_by_violation_rate_check_count_pos)
  have hbase_nonneg :
      0 ≤
        1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate := by
    exact sub_nonneg.mpr D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate_le_one
  have h_epsilon_le_violation' :
      D.epsilon ≤ D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate := by
    simpa [xi_linear_recurrence_local_test_by_violation_rate_violation_rate,
      xi_linear_recurrence_local_test_by_violation_rate_check_count] using
      D.h_epsilon_le_violation
  have hbase_le :
      1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate ≤ 1 - D.epsilon := by
    simpa using sub_le_sub_left h_epsilon_le_violation' 1
  have hpow_le :
      (1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate) ^ D.samples ≤
        (1 - D.epsilon) ^ D.samples := by
    exact pow_le_pow_left₀ hbase_nonneg hbase_le D.samples
  have hpass_le :
      (1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate) ^ D.samples ≤
        (1 / 3 : ℚ) := by
    exact le_trans hpow_le D.h_pass_probability_bound
  refine ⟨?_, ?_, ?_⟩
  · unfold
      xi_linear_recurrence_local_test_by_violation_rate_single_check_miss_probability
      xi_linear_recurrence_local_test_by_violation_rate_violation_rate
    field_simp [hcount_ne]
  · rfl
  · calc
      (2 / 3 : ℚ) = 1 - (1 / 3 : ℚ) := by norm_num
      _ ≤ 1 - (1 - D.xi_linear_recurrence_local_test_by_violation_rate_violation_rate) ^ D.samples := by
        linarith
      _ = D.xi_linear_recurrence_local_test_by_violation_rate_rejection_probability := by
        rfl

end Omega.Zeta

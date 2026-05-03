import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-coherence-stopping-time-leyang-k5`. -/
theorem paper_xi_coherence_stopping_time_leyang_k5 (N : ℕ) (hN : 1 ≤ N) :
    (19 / 20 : ℚ) + (∑ n ∈ Finset.Icc 2 N, (3 : ℚ) / (5 * (4 : ℚ) ^ n)) +
        1 / (5 * (4 : ℚ) ^ N) = 1 ∧
      (19 / 20 : ℚ) +
          (∑ n ∈ Finset.Icc 2 N, (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
        ((N : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ N)) =
          1 + (1 / 15 : ℚ) * (1 - 1 / (4 : ℚ) ^ N) := by
  refine Nat.le_induction ?base ?step N hN
  · norm_num
  · intro N hN ih
    have hIcc : 2 ≤ N + 1 := by omega
    have hmass_sum :
        (∑ n ∈ Finset.Icc 2 (N + 1), (3 : ℚ) / (5 * (4 : ℚ) ^ n)) =
          (∑ n ∈ Finset.Icc 2 N, (3 : ℚ) / (5 * (4 : ℚ) ^ n)) +
            (3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1)) := by
      rw [Finset.sum_Icc_succ_top hIcc]
    have hmean_sum :
        (∑ n ∈ Finset.Icc 2 (N + 1),
            (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) =
          (∑ n ∈ Finset.Icc 2 N, (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
            ((N + 1 : ℕ) : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1))) := by
      rw [Finset.sum_Icc_succ_top hIcc]
    have hpowN : (4 : ℚ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
    have hmass_tail :
        (3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1)) + 1 / (5 * (4 : ℚ) ^ (N + 1)) =
          1 / (5 * (4 : ℚ) ^ N) := by
      field_simp [pow_succ, hpowN]
      ring
    have hmean_tail :
        ((N + 1 : ℕ) : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1))) +
            (((N + 1 : ℕ) : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ (N + 1))) =
          ((N : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ N)) +
            1 / (5 * (4 : ℚ) ^ (N + 1)) := by
      field_simp [pow_succ, hpowN]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    have hrhs_step :
        1 + (1 / 15 : ℚ) * (1 - 1 / (4 : ℚ) ^ N) +
            1 / (5 * (4 : ℚ) ^ (N + 1)) =
          1 + (1 / 15 : ℚ) * (1 - 1 / (4 : ℚ) ^ (N + 1)) := by
      field_simp [pow_succ, hpowN]
      ring
    constructor
    · rw [hmass_sum]
      calc
        (19 / 20 : ℚ) +
              ((∑ n ∈ Finset.Icc 2 N, (3 : ℚ) / (5 * (4 : ℚ) ^ n)) +
                (3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1))) +
            1 / (5 * (4 : ℚ) ^ (N + 1)) =
            (19 / 20 : ℚ) +
              (∑ n ∈ Finset.Icc 2 N, (3 : ℚ) / (5 * (4 : ℚ) ^ n)) +
                ((3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1)) +
                  1 / (5 * (4 : ℚ) ^ (N + 1))) := by ring
        _ = (19 / 20 : ℚ) +
              (∑ n ∈ Finset.Icc 2 N, (3 : ℚ) / (5 * (4 : ℚ) ^ n)) +
                1 / (5 * (4 : ℚ) ^ N) := by rw [hmass_tail]
        _ = 1 := ih.1
    · rw [hmean_sum]
      calc
        (19 / 20 : ℚ) +
              ((∑ n ∈ Finset.Icc 2 N,
                  (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
                ((N + 1 : ℕ) : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1)))) +
            (((N + 1 : ℕ) : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ (N + 1))) =
            (19 / 20 : ℚ) +
              (∑ n ∈ Finset.Icc 2 N,
                (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
                (((N + 1 : ℕ) : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ (N + 1))) +
                  (((N + 1 : ℕ) : ℚ) + 1) *
                    (1 / (5 * (4 : ℚ) ^ (N + 1)))) := by ring
        _ = (19 / 20 : ℚ) +
              (∑ n ∈ Finset.Icc 2 N,
                (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
                (((N : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ N)) +
                  1 / (5 * (4 : ℚ) ^ (N + 1))) := by rw [hmean_tail]
        _ = (19 / 20 : ℚ) +
              (∑ n ∈ Finset.Icc 2 N,
                (n : ℚ) * ((3 : ℚ) / (5 * (4 : ℚ) ^ n))) +
                ((N : ℚ) + 1) * (1 / (5 * (4 : ℚ) ^ N)) +
              1 / (5 * (4 : ℚ) ^ (N + 1)) := by ring
        _ = 1 + (1 / 15 : ℚ) * (1 - 1 / (4 : ℚ) ^ N) +
              1 / (5 * (4 : ℚ) ^ (N + 1)) := by rw [ih.2]
        _ = 1 + (1 / 15 : ℚ) * (1 - 1 / (4 : ℚ) ^ (N + 1)) := hrhs_step

end Omega.Zeta

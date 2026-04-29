import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- The finite range of even exponents in a binomial expansion. -/
def xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange (n : ℕ) :
    Finset ℕ :=
  (Finset.range (n + 1)).filter Even

/-- Reindex a binomial sum over even exponents by half-exponents. -/
lemma xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_sum_even_reindex
    (a d : ℝ) (n : ℕ) :
    (∑ m ∈ xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange n,
        (Nat.choose n m : ℝ) * a ^ m * d ^ (n - m)) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℝ) * a ^ (2 * k) * d ^ (n - 2 * k) := by
  classical
  symm
  refine Finset.sum_bij (fun k _ => 2 * k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange, mem_filter]
    have hklt : k < n / 2 + 1 := by simpa using hk
    have hk_le : k ≤ n / 2 := Nat.lt_succ_iff.mp hklt
    constructor
    · simpa [mem_range] using
        Nat.lt_succ_of_le (le_trans (Nat.mul_le_mul_left 2 hk_le) (Nat.mul_div_le n 2))
    · exact even_two.mul_right k
  · intro k hk k₂ hk₂ h
    have hmul : 2 * k = 2 * k₂ := by simpa using h
    omega
  · intro m hm
    rw [xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange, mem_filter] at hm
    rcases hm with ⟨hm_lt, hm_even⟩
    rcases (even_iff_exists_two_mul.mp hm_even) with ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · simp only [mem_range]
      have hm_lt' : m < n + 1 := by simpa [mem_range] using hm_lt
      have hm_le : m ≤ n := Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hm_lt')
      have hmul_le : k * 2 ≤ n := by omega
      exact Nat.lt_succ_iff.mpr
        ((Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hmul_le)
    · simpa using hk.symm
  · intro k hk
    rfl

/-- Adding the two mirror branches cancels odd powers of the signed variable. -/
lemma xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_mirror_sum
    (a d : ℝ) (n : ℕ) :
    (a + d) ^ n + (-a + d) ^ n =
      2 * ∑ k ∈ Finset.range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℝ) * a ^ (2 * k) * d ^ (n - 2 * k) := by
  classical
  rw [add_pow, add_pow]
  rw [← Finset.sum_add_distrib]
  have hterm :
      (fun m =>
        a ^ m * d ^ (n - m) * (Nat.choose n m : ℝ) +
          (-a) ^ m * d ^ (n - m) * (Nat.choose n m : ℝ)) =
        fun m =>
          if Even m then 2 * ((Nat.choose n m : ℝ) * a ^ m * d ^ (n - m)) else 0 := by
    funext m
    by_cases hm : Even m
    · simp [hm, hm.neg_pow]
      ring
    · have hodd : Odd m := Nat.not_even_iff_odd.mp hm
      simp [hm, hodd.neg_pow]
  calc
    ∑ x ∈ range (n + 1),
        (a ^ x * d ^ (n - x) * (Nat.choose n x : ℝ) +
          (-a) ^ x * d ^ (n - x) * (Nat.choose n x : ℝ)) =
        ∑ x ∈ range (n + 1),
          if Even x then 2 * ((Nat.choose n x : ℝ) * a ^ x * d ^ (n - x)) else 0 := by
          simp_rw [hterm]
    _ = ∑ x ∈ xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange n,
          2 * ((Nat.choose n x : ℝ) * a ^ x * d ^ (n - x)) := by
          simp [xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange,
            Finset.sum_filter]
    _ = 2 * ∑ x ∈ xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange n,
          (Nat.choose n x : ℝ) * a ^ x * d ^ (n - x) := by
          rw [Finset.mul_sum]
    _ = 2 * ∑ k ∈ Finset.range (n / 2 + 1),
          (Nat.choose n (2 * k) : ℝ) * a ^ (2 * k) * d ^ (n - 2 * k) := by
          congr 1
          simpa [xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_evenRange]
            using xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_sum_even_reindex
              a d n

/-- Paper label: `thm:xi-time-part50cb-mirror-branch-evenodd-power-sum-suppression`. -/
theorem paper_xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression (a d : ℝ) (r : ℕ) :
    ((a + d) ^ (2 * r) + (-a + d) ^ (2 * r) =
        2 * ∑ k ∈ Finset.range (r + 1),
          (Nat.choose (2 * r) (2 * k) : ℝ) * a ^ (2 * k) * d ^ (2 * r - 2 * k)) ∧
      ((a + d) ^ (2 * r + 1) + (-a + d) ^ (2 * r + 1) =
        2 * ∑ k ∈ Finset.range (r + 1),
          (Nat.choose (2 * r + 1) (2 * k) : ℝ) * a ^ (2 * k) *
            d ^ (2 * r + 1 - 2 * k)) := by
  constructor
  · simpa [Nat.mul_div_right r (by decide : 0 < 2)] using
      xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_mirror_sum a d (2 * r)
  · have hdiv : (2 * r + 1) / 2 = r := by omega
    simpa [hdiv] using
      xi_time_part50cb_mirror_branch_evenodd_power_sum_suppression_mirror_sum a d (2 * r + 1)

end Omega.Zeta

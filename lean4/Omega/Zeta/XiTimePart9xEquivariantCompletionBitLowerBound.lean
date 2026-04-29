import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The total number of labels contributed by the nontrivial regular orbit quotients. -/
def xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count
    {ι : Type*} [Fintype ι] (k : ι → ℕ) : ℕ :=
  ∑ i, 2 ^ k i

/-- The rank contribution obtained by injecting the elementary abelian `2`-group into the product
of the nontrivial orbit quotients. -/
def xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_rank_sum
    {ι : Type*} [Fintype ι] (k : ι → ℕ) : ℕ :=
  ∑ i, k i

private theorem xi_time_part9x_equivariant_completion_bit_lower_bound_rank_vs_orbit_size
    (n : ℕ) (hn : 1 ≤ n) :
    n ≤ 2 ^ (n - 1) := by
  by_cases hpred : n - 1 = 0
  · have hone : n = 1 := by omega
    simp [hone]
  · have hpred_pos : 0 < n - 1 := Nat.pos_of_ne_zero hpred
    have hpow : n - 1 < 2 ^ (n - 1) := Nat.lt_pow_self (by norm_num : 1 < 2)
    omega

private theorem xi_time_part9x_equivariant_completion_bit_lower_bound_double_half_sum
    {ι : Type*} [Fintype ι] (k : ι → ℕ) (hpos : ∀ i, 1 ≤ k i) :
    2 * (∑ i, 2 ^ (k i - 1)) = ∑ i, 2 ^ k i := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hpos i)) with ⟨m, hm⟩
  rw [hm]
  simp [pow_succ, two_mul, Nat.mul_comm]

/-- Paper label: `thm:xi-time-part9x-equivariant-completion-bit-lower-bound`.
If a faithful elementary abelian `2`-group of rank `r` injects into the product of the nontrivial
regular orbit quotients, and those nontrivial orbits occupy at most the `2^B` labels of a
`B`-bit completion, then `r ≤ 2^(B-1)`. The same estimate yields the boundary-center and
full-center corollaries `B ≥ 3` and `B ≥ 4` for ranks `3` and `8`. -/
theorem paper_xi_time_part9x_equivariant_completion_bit_lower_bound
    {ι : Type*} [Fintype ι]
    (r B : ℕ)
    (k : ι → ℕ)
    (hfaithful :
      r ≤ xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_rank_sum k)
    (hpos : ∀ i, 1 ≤ k i)
    (hbudget :
      xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count k ≤ 2 ^ B) :
    r ≤ 2 ^ (B - 1) ∧
      ((3 : ℕ) ≤ r → 3 ≤ B) ∧
      ((8 : ℕ) ≤ r → 4 ≤ B) := by
  classical
  let halfSum : ℕ := ∑ i, 2 ^ (k i - 1)
  have hsum_le_half :
      xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_rank_sum k ≤ halfSum := by
    dsimp [xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_rank_sum, halfSum]
    refine Finset.sum_le_sum ?_
    intro i hi
    exact xi_time_part9x_equivariant_completion_bit_lower_bound_rank_vs_orbit_size (k i) (hpos i)
  have hdouble :
      2 * halfSum = xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count k := by
    dsimp [halfSum, xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count]
    exact xi_time_part9x_equivariant_completion_bit_lower_bound_double_half_sum k hpos
  have hhalf_le : halfSum ≤ 2 ^ (B - 1) := by
    cases B with
    | zero =>
        have hsmall : 2 * halfSum ≤ 1 := by
          calc
            2 * halfSum =
                xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count k := hdouble
            _ ≤ 2 ^ 0 := by simpa using hbudget
            _ = 1 := by norm_num
        omega
    | succ b =>
        have hsmall : 2 * halfSum ≤ 2 * 2 ^ b := by
          calc
            2 * halfSum =
                xi_time_part9x_equivariant_completion_bit_lower_bound_orbit_label_count k := hdouble
            _ ≤ 2 ^ (b + 1) := by simpa using hbudget
            _ = 2 * 2 ^ b := by simp [pow_succ, Nat.mul_comm]
        have : halfSum ≤ 2 ^ b := by omega
        simpa using this
  have hr_le : r ≤ 2 ^ (B - 1) := le_trans hfaithful (le_trans hsum_le_half hhalf_le)
  refine ⟨hr_le, ⟨?_, ?_⟩⟩
  · intro hthree
    have hbound : 3 ≤ 2 ^ (B - 1) := le_trans hthree hr_le
    by_cases hB : B ≤ 2
    · have hcases : B = 0 ∨ B = 1 ∨ B = 2 := by omega
      rcases hcases with rfl | rfl | rfl <;> simp at hbound
    · exact by omega
  · intro height
    have hbound : 8 ≤ 2 ^ (B - 1) := le_trans height hr_le
    by_cases hB : B ≤ 3
    · have hcases : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;> simp at hbound
    · exact by omega

end Omega.Zeta

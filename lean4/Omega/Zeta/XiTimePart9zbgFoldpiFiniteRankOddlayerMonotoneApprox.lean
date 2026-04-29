import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

theorem paper_xi_time_part9zbg_foldpi_finite_rank_oddlayer_monotone_approx {r N : ℕ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) ^ (2 * r))) <
      ∑ n ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / ((n : ℝ) ^ (2 * r)) := by
  have _ : 1 ≤ r := hr
  have _ : 1 ≤ N := hN
  rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega)]
  have hbase : 0 < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hpow : 0 < ((N + 1 : ℕ) : ℝ) ^ (2 * r) := pow_pos hbase _
  exact lt_add_of_pos_right _ (one_div_pos.mpr hpow)

end Omega.Zeta

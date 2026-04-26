import Mathlib.Tactic

namespace Omega.Zeta

private theorem xi_symq_golden_cq_determinantal_divisors_list_range_sum_eq_finset
    (k : Nat) :
    (List.range k).sum = (Finset.range k).sum fun i => i := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, Finset.sum_range_succ, List.sum_append, ih]
      simp

private theorem xi_symq_golden_cq_determinantal_divisors_list_range_sum (k : Nat) :
    (List.range k).sum = k * (k - 1) / 2 := by
  rw [xi_symq_golden_cq_determinantal_divisors_list_range_sum_eq_finset k]
  exact Finset.sum_range_id k

/-- Paper label: `cor:xi-symq-golden-cq-determinantal-divisors`. Once the Smith staircase
identifies the first `k` exponents with `0, ..., k - 1`, their sum is the triangular number. -/
theorem paper_xi_symq_golden_cq_determinantal_divisors
    (q : Nat) (detDivExp : Nat -> Nat)
    (hsmith : forall k, 1 <= k -> k <= q + 1 -> detDivExp k = (List.range k).sum) :
    forall k, 1 <= k -> k <= q + 1 -> detDivExp k = k * (k - 1) / 2 := by
  intro k hk hle
  rw [hsmith k hk hle]
  exact xi_symq_golden_cq_determinantal_divisors_list_range_sum k

end Omega.Zeta

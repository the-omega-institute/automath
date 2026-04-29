import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-sequence-layer-constant-periodic-defect-cannot-replace-clarity-budget`.
A bounded nonnegative defect divided by an eventually positive sequence tending to infinity is
eventually at most any positive tolerance. -/
theorem paper_conclusion_sequence_layer_constant_periodic_defect_cannot_replace_clarity_budget
    (delta : Real) (n : Nat -> Real) (hdelta : 0 <= delta)
    (hn_pos : exists N0 : Nat, forall k : Nat, N0 <= k -> 0 < n k)
    (hn_unbounded : forall B : Real, exists N : Nat, forall k : Nat, N <= k -> B <= n k) :
    forall eps : Real, 0 < eps -> exists N : Nat, forall k : Nat, N <= k ->
      delta / n k <= eps := by
  intro eps heps
  have hdelta_nonneg : 0 <= delta := hdelta
  rcases hn_pos with ⟨N0, hn_pos'⟩
  rcases hn_unbounded (delta / eps) with ⟨N1, hn_large⟩
  refine ⟨max N0 N1, ?_⟩
  intro k hk
  have hk0 : N0 <= k := le_trans (Nat.le_max_left N0 N1) hk
  have hk1 : N1 <= k := le_trans (Nat.le_max_right N0 N1) hk
  have hn_pos_k : 0 < n k := hn_pos' k hk0
  have hn_large_k : delta / eps <= n k := hn_large k hk1
  have hdelta_le : delta <= eps * n k := by
    calc
      delta = (delta / eps) * eps := by field_simp [ne_of_gt heps]
      _ <= n k * eps := mul_le_mul_of_nonneg_right hn_large_k heps.le
      _ = eps * n k := by ring
  exact (div_le_iff₀ hn_pos_k).2 (by nlinarith [hdelta_nonneg, hdelta_le])

end Omega.Conclusion

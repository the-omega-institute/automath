import Omega.Conclusion.AffineRegisterBudget

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a divergence-completion register exists exactly when the external register
    budget has at least `p^r` states.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem paper_conclusion_boundary_cycle_rank_external_info_lower_bound_seeds
    (p r R : ℕ) :
    (∃ f : Fin (p ^ r) → Fin R, Function.Injective f) ↔ p ^ r ≤ R := by
  constructor
  · exact registerBudget_min_card p r R
  · intro h
    have hcard : Fintype.card (Fin (p ^ r)) ≤ Fintype.card (Fin R) := by
      simpa [Fintype.card_fin] using h
    rcases Function.Embedding.nonempty_of_card_le hcard with ⟨f⟩
    exact ⟨f, f.injective⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing lower-bound package together with the sharp identity witness.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem paper_conclusion_boundary_cycle_rank_external_info_lower_bound
    (p r R : Nat) :
    ((∃ f : Fin (p ^ r) → Fin R, Function.Injective f) → p ^ r ≤ R) ∧
      (∃ f : Fin (p ^ r) → Fin (p ^ r), Function.Injective f) := by
  exact ⟨registerBudget_lower_bound p r R, registerBudget_sharp p r⟩

set_option maxHeartbeats 400000 in
/-- Transcript-plus-register encodings of a `p^r`-state boundary fiber into
    `p^q × (E+1)^k` force the expected product-cardinality lower bound.
    cor:conclusion-boundary-query-register-budget-exponential-law -/
theorem paper_conclusion_boundary_query_register_budget_exponential_law
    (p q r k E : Nat)
    (encode : Fin (p ^ r) -> Prod (Fin (p ^ q)) (Fin ((E + 1) ^ k)))
    (hinj : Function.Injective encode) :
    p ^ r <= p ^ q * (E + 1) ^ k := by
  simpa [Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_le_of_injective encode hinj

set_option maxHeartbeats 400000 in
/-- Paper-facing conclusion: once the upper and lower query-complexity bounds are both
    established, the minimum boundary path-independence query complexity is exactly the first
    Betti rank.
    thm:conclusion-boundary-path-independence-query-complexity-equals-betti -/
theorem paper_conclusion_boundary_path_independence_query_complexity_equals_betti
    (QminB rB : ℕ) (hUpper : QminB ≤ rB) (hLower : rB ≤ QminB) : QminB = rB := by
  exact Nat.le_antisymm hUpper hLower

end Omega.Conclusion

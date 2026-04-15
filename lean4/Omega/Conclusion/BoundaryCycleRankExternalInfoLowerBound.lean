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

end Omega.Conclusion

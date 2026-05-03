import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-bounded-ellipse-family-realized-by-rank-two-tate-carpet`. -/
theorem paper_conclusion_bounded_ellipse_family_realized_by_rank_two_tate_carpet
    (k M B : ℕ) (hMB : M < B) :
    Fintype.card (Fin k → Fin (M + 1) × Fin (M + 1)) = (M + 1) ^ (2 * k) := by
  have _ := hMB
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_two (M + 1), ← pow_mul]

end Omega.Conclusion

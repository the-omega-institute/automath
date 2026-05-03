import Mathlib.Tactic

namespace Omega.Conclusion

/-- The one-digit threshold condition for affine word values with digits `0, ..., M`. -/
def conclusion_tate_rank_digit_threshold_orthogonality_digitFits (C M : ℕ) : Prop :=
  ∀ a : Fin (M + 1), a.val < C

/-- Paper-facing package for the two independent resource axes: cardinal rank two is detected by
the finite rank model `Fin 2`, while the digit axis is exactly the inequality `M < C`. -/
def conclusion_tate_rank_digit_threshold_orthogonality_statement : Prop :=
  (∀ r : ℕ, Fintype.card (Fin r) = Fintype.card (Fin 2) → r = 2) ∧
    (∀ C M : ℕ,
      conclusion_tate_rank_digit_threshold_orthogonality_digitFits C M ↔ M < C) ∧
    (∀ r : ℕ, r ≠ 2 → Fintype.card (Fin r) ≠ Fintype.card (Fin 2)) ∧
    (∀ C M : ℕ, C ≤ M → ¬ conclusion_tate_rank_digit_threshold_orthogonality_digitFits C M)

/-- Paper label:
`thm:conclusion-tate-rank-digit-threshold-orthogonality`. -/
theorem paper_conclusion_tate_rank_digit_threshold_orthogonality :
    conclusion_tate_rank_digit_threshold_orthogonality_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hcard
    simpa using hcard
  · intro C M
    constructor
    · intro hfits
      simpa using hfits ⟨M, Nat.lt_succ_self M⟩
    · intro hMC a
      exact lt_of_lt_of_le a.isLt (Nat.succ_le_of_lt hMC)
  · intro r hr hcard
    exact hr (by simpa using hcard)
  · intro C M hCM hfits
    have hMC : M < C := by
      simpa using hfits ⟨M, Nat.lt_succ_self M⟩
    exact (not_lt_of_ge hCM) hMC

end Omega.Conclusion

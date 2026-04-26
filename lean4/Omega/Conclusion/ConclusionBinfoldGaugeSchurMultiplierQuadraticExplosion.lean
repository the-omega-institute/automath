import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete bin-fold gauge data for the Schur-multiplier rank count. -/
structure conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_data where
  n : ℕ → ℕ
  minFiberSize : ℕ → ℕ
  schurMultiplierRank : ℕ → ℕ
  threshold : ℕ
  h_eventual_seven :
    ∀ m, threshold ≤ m → 7 ≤ minFiberSize m
  h_symmetric_factor_count :
    ∀ m, 7 ≤ minFiberSize m → schurMultiplierRank m = n m + Nat.choose (n m) 2

lemma conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_diagonal_pair_count
    (n : ℕ) :
    n + Nat.choose n 2 = n * (n + 1) / 2 := by
  calc
    n + Nat.choose n 2 = Nat.choose n 1 + Nat.choose n 2 := by
      rw [Nat.choose_one_right]
    _ = Nat.choose (n + 1) 2 := by
      rw [Nat.choose_succ_succ]
    _ = (n + 1) * ((n + 1) - 1) / 2 := by
      rw [Nat.choose_two_right]
    _ = n * (n + 1) / 2 := by
      cases n <;> simp [Nat.mul_comm]

/-- Paper label:
`thm:conclusion-binfold-gauge-schur-multiplier-quadratic-explosion`. -/
theorem paper_conclusion_binfold_gauge_schur_multiplier_quadratic_explosion
    (D : conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_data) :
    ∃ m0, ∀ m, m0 ≤ m →
      D.schurMultiplierRank m = D.n m * (D.n m + 1) / 2 := by
  refine ⟨D.threshold, ?_⟩
  intro m hm
  rw [D.h_symmetric_factor_count m (D.h_eventual_seven m hm)]
  exact conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_diagonal_pair_count (D.n m)

end Omega.Conclusion

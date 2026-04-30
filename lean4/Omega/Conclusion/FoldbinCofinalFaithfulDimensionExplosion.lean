import Mathlib.Tactic

namespace Omega.Conclusion

/-- Natural numbers are bounded by their base-two exponential. -/
theorem conclusion_foldbin_cofinal_faithful_dimension_explosion_nat_le_two_pow (n : ℕ) :
    n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow_pos : 1 ≤ 2 ^ n := by
        exact Nat.pow_pos (by decide : 0 < 2)
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left hpow_pos (2 ^ n)
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Paper label: `cor:conclusion-foldbin-cofinal-faithful-dimension-explosion`. -/
theorem paper_conclusion_foldbin_cofinal_faithful_dimension_explosion
    (m dim : ℕ → ℕ)
    (hcofinal : ∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B ≤ m j)
    (hdim : ∀ j : ℕ, 2 ^ (m j) ≤ dim j) :
    ∀ B : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → B ≤ dim j := by
  intro B
  rcases hcofinal B with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro j hj
  exact le_trans (hJ j hj)
    (le_trans (conclusion_foldbin_cofinal_faithful_dimension_explosion_nat_le_two_pow (m j))
      (hdim j))

end Omega.Conclusion

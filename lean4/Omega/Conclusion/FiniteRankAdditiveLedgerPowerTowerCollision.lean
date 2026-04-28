import Mathlib.Algebra.Group.Nat.Defs

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-rank-additive-ledger-power-tower-collision`. -/
theorem paper_conclusion_finite_rank_additive_ledger_power_tower_collision
    {A : Type*} [AddCommMonoid A] (Ψ : ℕ → A)
    (hMul : ∀ a b : ℕ, Ψ (a * b) = Ψ a + Ψ b)
    (hcollision : ∃ u v : ℕ, u ≠ v ∧ Ψ u = Ψ v) :
    ∃ u v : ℕ, u ≠ v ∧ ∀ t : ℕ, 1 ≤ t → Ψ (u ^ t) = Ψ (v ^ t) := by
  have hpow : ∀ a n : ℕ, Ψ (a ^ (n + 1)) = (n + 1) • Ψ a := by
    intro a n
    induction n with
    | zero =>
        rw [Nat.pow_one]
        exact (one_nsmul (Ψ a)).symm
    | succ n ih =>
        rw [Nat.pow_succ, hMul, ih]
        exact (AddMonoid.nsmul_succ (n + 1) (Ψ a)).symm
  rcases hcollision with ⟨u, v, huv, huvΨ⟩
  refine ⟨u, v, huv, ?_⟩
  intro t ht
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt ht) with ⟨n, rfl⟩
  calc
    Ψ (u ^ (n + 1)) = (n + 1) • Ψ u := hpow u n
    _ = (n + 1) • Ψ v := by rw [huvΨ]
    _ = Ψ (v ^ (n + 1)) := (hpow v n).symm

end Omega.Conclusion

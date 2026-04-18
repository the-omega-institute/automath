import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The multiplicative branch budget of a finite prime-adjoining chain. -/
def primeAdjunctionBudget {r : ℕ} (M : Fin r → ℕ) : ℕ :=
  ∏ i, M i

/-- Reindex the prime-adjoining chain by a permutation of its finite stages. -/
def primeAdjunctionPermute {r : ℕ} (p : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) : Fin r → ℕ :=
  p ∘ σ

/-- Paper-facing exact multiplicative budget for a finite prime-adjoining chain: pointwise lower
bounds multiply, equality is realized by choosing the minimal implementation at every stage, and
the product is unchanged by reordering the finite chain.
    thm:conclusion-prime-adjunction-exact-multiplicative-budget -/
theorem paper_conclusion_prime_adjunction_exact_multiplicative_budget {r : ℕ}
    (p M : Fin r → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hstep : ∀ i, p i ≤ M i) :
    primeAdjunctionBudget p ≤ primeAdjunctionBudget M ∧
    (∃ Mmin : Fin r → ℕ, Mmin = p ∧ primeAdjunctionBudget Mmin = primeAdjunctionBudget p) ∧
    (∀ σ : Equiv.Perm (Fin r),
      primeAdjunctionBudget (primeAdjunctionPermute p σ) = primeAdjunctionBudget p) ∧
    0 < primeAdjunctionBudget p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [primeAdjunctionBudget] using
      (Finset.prod_le_prod' (s := Finset.univ) fun i _ => hstep i)
  · exact ⟨p, rfl, rfl⟩
  · intro σ
    simpa [primeAdjunctionBudget, primeAdjunctionPermute] using (Equiv.prod_comp σ p)
  · unfold primeAdjunctionBudget
    exact Finset.prod_pos fun i _ => Nat.Prime.pos (hp i)

end Omega.Conclusion

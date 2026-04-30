import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- Concrete data for the unbounded-prime-support obstruction.  The route supplies infinitely
many distinct prime witnesses, and its valuation ledger is a finitely supported prime-exponent
vector with the recorded uniqueness property. -/
structure conclusion_unbounded_prime_support_no_finite_register_embedding_Data where
  conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness : ℕ → ℕ
  conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness_prime :
    ∀ n, Nat.Prime
      (conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness n)
  conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness_injective :
    Function.Injective
      conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness
  conclusion_unbounded_prime_support_no_finite_register_embedding_valuationLedger :
    (ℕ →₀ ℕ) → (ℕ →₀ ℕ)
  conclusion_unbounded_prime_support_no_finite_register_embedding_uniqueFactorization :
    ∀ x y,
      conclusion_unbounded_prime_support_no_finite_register_embedding_valuationLedger x =
          conclusion_unbounded_prime_support_no_finite_register_embedding_valuationLedger y →
        x = y

namespace conclusion_unbounded_prime_support_no_finite_register_embedding_Data

/-- The finite-support basis element attached to the `n`th distinct prime witness. -/
noncomputable def conclusion_unbounded_prime_support_no_finite_register_embedding_basisElement
    (D : conclusion_unbounded_prime_support_no_finite_register_embedding_Data) (n : ℕ) :
  ℕ →₀ ℕ :=
  Finsupp.single
    (D.conclusion_unbounded_prime_support_no_finite_register_embedding_primeWitness n) 1

/-- A finite-register embedding would compress the first `k+1` distinct basis elements into
only `k` registers while still separating them. -/
def conclusion_unbounded_prime_support_no_finite_register_embedding_embedsInFiniteRegister
    (D : conclusion_unbounded_prime_support_no_finite_register_embedding_Data) (k : ℕ) :
    Prop :=
  ∃ register : (ℕ →₀ ℕ) → Fin k,
    Function.Injective fun i : Fin (k + 1) =>
      register (D.conclusion_unbounded_prime_support_no_finite_register_embedding_basisElement i.1)

end conclusion_unbounded_prime_support_no_finite_register_embedding_Data

open conclusion_unbounded_prime_support_no_finite_register_embedding_Data

/-- Paper label:
`thm:conclusion-unbounded-prime-support-no-finite-register-embedding`. -/
theorem paper_conclusion_unbounded_prime_support_no_finite_register_embedding
    (D : conclusion_unbounded_prime_support_no_finite_register_embedding_Data) :
    (∀ k : ℕ,
        ¬ D.conclusion_unbounded_prime_support_no_finite_register_embedding_embedsInFiniteRegister
          k) ∧
      Function.Injective
        D.conclusion_unbounded_prime_support_no_finite_register_embedding_valuationLedger := by
  refine ⟨?_, ?_⟩
  · intro k
    rintro ⟨register, hregister⟩
    have hcard :
        Fintype.card (Fin (k + 1)) ≤ Fintype.card (Fin k) :=
      Fintype.card_le_of_injective
        (fun i : Fin (k + 1) =>
          register
            (D.conclusion_unbounded_prime_support_no_finite_register_embedding_basisElement i.1))
        hregister
    simp at hcard
  · intro x y hxy
    exact
      D.conclusion_unbounded_prime_support_no_finite_register_embedding_uniqueFactorization x y hxy

end Omega.Conclusion

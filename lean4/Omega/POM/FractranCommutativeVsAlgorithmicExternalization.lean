import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.POM.FractranPermutationEmbeddingLength

namespace Omega.POM

/-- The fiber permutation subgroup `Aut(π)` consists of the permutations of `Fin n` preserving the
fiber map `π`. -/
def fiberPermutationSubgroup {n : ℕ} {X : Type*} (π : Fin n → X) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i, π (σ i) = π i}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ i
    calc
      π (σ (τ i)) = π (τ i) := hσ (τ i)
      _ = π i := hτ i
  inv_mem' := by
    intro σ hσ i
    simpa using (hσ (σ⁻¹ i)).symm

/-- Paper label: `prop:pom-fractran-commutative-vs-algorithmic-externalization`. Every homomorphism
from `Aut(π)` to a commutative group factors through abelianization, while the prime-core
permutation embedding restricts faithfully from the full symmetric group to the fiber permutation
subgroup. -/
theorem paper_pom_fractran_commutative_vs_algorithmic_externalization
    {n : ℕ} {X : Type*} (π : Fin n → X) :
    (∀ {A : Type*} [CommGroup A], ∀ ρ : fiberPermutationSubgroup π →* A,
      ∃ ρbar : Abelianization (fiberPermutationSubgroup π) →* A,
        ρ = ρbar.comp Abelianization.of) ∧
      ∃ encode : Fin n ↪ Nat, ∃ compile : fiberPermutationSubgroup π → List (Nat × Nat),
        (∀ i, Nat.Prime (encode i)) ∧
          Function.Injective
            (fun σ : fiberPermutationSubgroup π =>
              fun i : Fin n => primecoreStep (compile σ) (encode i)) ∧
          (∀ σ τ i,
            primecoreStep (compile (σ * τ)) (encode i) =
              primecoreStep (compile σ) (primecoreStep (compile τ) (encode i))) ∧
          (∀ σ i, primecoreStep (compile σ) (encode i) = encode (σ.1 i)) ∧
          (∀ σ, (compile σ).length = n) := by
  rcases paper_pom_fractran_permutation_embedding_length n with
    ⟨encode, compile, hPrime, hInjective, hComp, hEval, hLen, _hMin⟩
  refine ⟨?_, ?_⟩
  · intro A _ ρ
    refine ⟨Abelianization.lift ρ, ?_⟩
    ext σ
    simp
  · refine ⟨encode, fun σ => compile σ.1, hPrime, ?_, ?_, ?_, ?_⟩
    · intro σ τ hστ
      apply Subtype.ext
      exact hInjective hστ
    · intro σ τ i
      exact hComp σ.1 τ.1 i
    · intro σ i
      exact hEval σ.1 i
    · intro σ
      exact hLen σ.1

end Omega.POM

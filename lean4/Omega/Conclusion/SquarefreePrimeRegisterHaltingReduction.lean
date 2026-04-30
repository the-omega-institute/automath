import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped Classical

/-- Certificate choices from the first `B` prime labels, represented as subsets of `Fin B`. -/
abbrev conclusion_squarefree_prime_register_halting_reduction_certificateSpace (B : ℕ) :=
  Finset (Fin B)

/-- A uniform finite squarefree-register budget injects every fiber into the finite certificate
space determined by some bounded prime prefix. -/
def conclusion_squarefree_prime_register_halting_reduction_hasRegister
    (sizes : ℕ → ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ,
    ∃ code :
      Fin (sizes n) →
        Fin (Fintype.card
          (conclusion_squarefree_prime_register_halting_reduction_certificateSpace B)),
      Function.Injective code

lemma conclusion_squarefree_prime_register_halting_reduction_certificate_card (B : ℕ) :
    Fintype.card
        (conclusion_squarefree_prime_register_halting_reduction_certificateSpace B) =
      2 ^ B := by
  simp [conclusion_squarefree_prime_register_halting_reduction_certificateSpace]

lemma conclusion_squarefree_prime_register_halting_reduction_bounded_gives_register
    {sizes : ℕ → ℕ} (hbounded : ∃ B : ℕ, ∀ n : ℕ, sizes n ≤ 2 ^ B) :
    conclusion_squarefree_prime_register_halting_reduction_hasRegister sizes := by
  rcases hbounded with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  have hle :
      sizes n ≤
        Fintype.card
          (conclusion_squarefree_prime_register_halting_reduction_certificateSpace B) := by
    rw [conclusion_squarefree_prime_register_halting_reduction_certificate_card]
    exact hB n
  exact ⟨Fin.castLE hle, Fin.castLE_injective hle⟩

lemma conclusion_squarefree_prime_register_halting_reduction_register_gives_bounded
    {sizes : ℕ → ℕ}
    (hregister : conclusion_squarefree_prime_register_halting_reduction_hasRegister sizes) :
    ∃ B : ℕ, ∀ n : ℕ, sizes n ≤ 2 ^ B := by
  rcases hregister with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  rcases hB n with ⟨code, hcode⟩
  have hcard :=
    Fintype.card_le_of_injective code hcode
  simpa [conclusion_squarefree_prime_register_halting_reduction_certificate_card] using hcard

/-- Paper label: `cor:conclusion-squarefree-prime-register-halting-reduction`.
Finite squarefree certificates over the first `B` prime labels have cardinality `2^B`; hence a
bounded-prime certificate family is equivalent to a finite injectivizing register. A halting
reduction to that bounded-prime condition transfers undecidability to deciding whether such a
finite register exists. -/
theorem paper_conclusion_squarefree_prime_register_halting_reduction
    {Code : Type*} (fiberSize : Code → ℕ → ℕ) (halts : Code → Prop)
    (hReduction : ∀ c : Code, halts c ↔ ∃ B : ℕ, ∀ n : ℕ, fiberSize c n ≤ 2 ^ B)
    (hUndecidable : ¬ Nonempty (∀ c : Code, Decidable (halts c))) :
    (∀ B : ℕ,
      Fintype.card
          (conclusion_squarefree_prime_register_halting_reduction_certificateSpace B) =
        2 ^ B) ∧
      (∀ c : Code,
        (∃ B : ℕ, ∀ n : ℕ, fiberSize c n ≤ 2 ^ B) →
          conclusion_squarefree_prime_register_halting_reduction_hasRegister (fiberSize c)) ∧
      (∀ c : Code,
        conclusion_squarefree_prime_register_halting_reduction_hasRegister (fiberSize c) →
          ∃ B : ℕ, ∀ n : ℕ, fiberSize c n ≤ 2 ^ B) ∧
      ¬ Nonempty
        (∀ c : Code,
          Decidable
            (conclusion_squarefree_prime_register_halting_reduction_hasRegister (fiberSize c))) := by
  refine ⟨conclusion_squarefree_prime_register_halting_reduction_certificate_card, ?_, ?_, ?_⟩
  · intro c
    exact conclusion_squarefree_prime_register_halting_reduction_bounded_gives_register
  · intro c
    exact conclusion_squarefree_prime_register_halting_reduction_register_gives_bounded
  · intro hDecRegister
    apply hUndecidable
    refine ⟨?_⟩
    intro c
    classical
    let P : Prop :=
      conclusion_squarefree_prime_register_halting_reduction_hasRegister (fiberSize c)
    have hIff :
        P ↔ ∃ B : ℕ, ∀ n : ℕ, fiberSize c n ≤ 2 ^ B := by
      constructor
      · exact conclusion_squarefree_prime_register_halting_reduction_register_gives_bounded
      · exact conclusion_squarefree_prime_register_halting_reduction_bounded_gives_register
    by_cases hp : P
    · exact isTrue ((hReduction c).mpr (hIff.mp hp))
    · exact isFalse (fun hhalt => hp (hIff.mpr ((hReduction c).mp hhalt)))

end Omega.Conclusion

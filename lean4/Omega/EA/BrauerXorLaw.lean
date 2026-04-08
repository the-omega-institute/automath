import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace Omega.EA

open scoped symmDiff

/-- Symmetric difference is commutative.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_comm (A B : Finset ℕ) : A ∆ B = B ∆ A :=
  symmDiff_comm A B

/-- Symmetric difference with itself is empty.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_self (A : Finset ℕ) : A ∆ A = ∅ :=
  symmDiff_self A

/-- Symmetric difference with the empty set is the identity.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_empty (A : Finset ℕ) : A ∆ (∅ : Finset ℕ) = A :=
  symmDiff_bot A

/-- Symmetric difference is associative.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_assoc (A B C : Finset ℕ) :
    (A ∆ B) ∆ C = A ∆ (B ∆ C) :=
  symmDiff_assoc A B C

/-- Cardinality of a symmetric difference.
    thm:prime-register-brauer-xor-law -/
theorem finset_card_symmDiff (A B : Finset ℕ) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hsd : A ∆ B = (A ∪ B) \ (A ∩ B) := symmDiff_eq_sup_sdiff_inf A B
  have hsub : A ∩ B ⊆ A ∪ B := by
    intro x hx
    rw [Finset.mem_inter] at hx
    exact Finset.mem_union.mpr (Or.inl hx.1)
  have hunion : (A ∆ B).card = (A ∪ B).card - (A ∩ B).card := by
    rw [hsd]
    have := @Finset.card_sdiff _ (A ∩ B) (A ∪ B) _
    -- `this : ((A ∪ B) \ (A ∩ B)).card = (A ∪ B).card - ((A ∩ B) ∩ (A ∪ B)).card`
    rw [show (A ∩ B) ∩ (A ∪ B) = A ∩ B from Finset.inter_eq_left.mpr hsub] at this
    exact this
  have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hle : (A ∩ B).card ≤ (A ∪ B).card := Finset.card_le_card hsub
  omega

/-- Cardinality of symmetric difference, mod 2.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_card_mod_two (A B : Finset ℕ) :
    (A ∆ B).card % 2 = (A.card + B.card) % 2 := by
  have := finset_card_symmDiff A B
  omega

/-- Even-cardinality subsets are closed under symmetric difference.
    thm:prime-register-brauer-xor-law -/
theorem finset_symmDiff_card_even_of_even (A B : Finset ℕ)
    (hA : A.card % 2 = 0) (hB : B.card % 2 = 0) :
    (A ∆ B).card % 2 = 0 := by
  rw [finset_symmDiff_card_mod_two]
  omega

/-- The empty Finset has even cardinality.
    thm:prime-register-brauer-xor-law -/
theorem empty_card_even : (∅ : Finset ℕ).card % 2 = 0 := by simp

/-- The predicate "a Finset has even cardinality".
    thm:prime-register-brauer-xor-law -/
def EvenCardFinset (S : Finset ℕ) : Prop := S.card % 2 = 0

/-- Paper package: Brauer XOR law skeleton on (Finset ℕ, ∆) with the
    even-cardinality subgroup closed under symmetric difference.
    thm:prime-register-brauer-xor-law -/
theorem paper_prime_register_brauer_xor_law :
    (∀ A B : Finset ℕ, A ∆ B = B ∆ A) ∧
    (∀ A : Finset ℕ, A ∆ A = ∅) ∧
    (∀ A : Finset ℕ, A ∆ (∅ : Finset ℕ) = A) ∧
    (∀ A B C : Finset ℕ, (A ∆ B) ∆ C = A ∆ (B ∆ C)) ∧
    (∀ A B : Finset ℕ,
      EvenCardFinset A → EvenCardFinset B → EvenCardFinset (A ∆ B)) ∧
    EvenCardFinset (∅ : Finset ℕ) :=
  ⟨finset_symmDiff_comm, finset_symmDiff_self, finset_symmDiff_empty,
   finset_symmDiff_assoc, finset_symmDiff_card_even_of_even, empty_card_even⟩

end Omega.EA

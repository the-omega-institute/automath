import Mathlib.Tactic

namespace Omega.SPG

/-- Proposition-valued wrapper for decidability of a binary relation. -/
def RelationDecidable {α : Type*} (R : α → α → Prop) : Prop :=
  Nonempty (∀ A B, Decidable (R A B))

/-- If an equivalence relation admits a finite-valued complete invariant, then it is decidable.
    Hence an undecidable relation admits no such invariant.
    prop:spg-undecidable-no-finite-computable-complete-invariant -/
theorem paper_spg_undecidable_no_finite_computable_complete_invariant {α : Type*}
    (R : α → α → Prop) (hUndecidable : ¬ RelationDecidable R) :
    ¬ ∃ M : Nat, ∃ I : α → Fin M, ∀ A B, R A B ↔ I A = I B := by
  intro h
  rcases h with ⟨M, I, hI⟩
  apply hUndecidable
  exact ⟨fun A B => decidable_of_iff (I A = I B) (hI A B).symm⟩

end Omega.SPG

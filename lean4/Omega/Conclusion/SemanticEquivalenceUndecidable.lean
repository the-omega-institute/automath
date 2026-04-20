import Mathlib.Tactic

namespace Omega.Conclusion

/-- A binary relation is pointwise decidable when every pair admits a `Decidable` instance. -/
def RelationPointwiseDecidable {α : Type*} (r : α → α → Prop) : Prop :=
  Nonempty (∀ x y, Decidable (r x y))

/-- A unary predicate is pointwise decidable when every input admits a `Decidable` instance. -/
def PredicatePointwiseDecidable {α : Type*} (p : α → Prop) : Prop :=
  Nonempty (∀ x, Decidable (p x))

/-- A reduction from an undecidable non-halting predicate to semantic equivalence transfers
undecidability to the semantic-equivalence problem. The proof is abstract and only uses the given
reduction against the fixed reference program `ref`.
    thm:conclusion-semantic-equivalence-undecidable -/
theorem paper_conclusion_semantic_equivalence_undecidable {Code Func : Type*}
    (semEq : Func → Func → Prop) (embed : Code → Func) (ref : Func) (nonHalting : Code → Prop)
    (hReduction : ∀ c, nonHalting c ↔ semEq (embed c) ref)
    (hUndecidable : ¬ Nonempty (∀ c, Decidable (nonHalting c))) :
    ¬ Nonempty (∀ f g, Decidable (semEq f g)) := by
  classical
  intro hSemEq
  apply hUndecidable
  refine ⟨?_⟩
  intro c
  let hDecEq : ∀ f g, Decidable (semEq f g) := Classical.choice hSemEq
  letI := hDecEq (embed c) ref
  exact decidable_of_iff (semEq (embed c) ref) (hReduction c).symm

end Omega.Conclusion

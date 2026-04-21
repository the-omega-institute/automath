import Mathlib.Tactic

namespace Omega.POM

namespace Setoid

/-- Minimal seed matching the theorem header: when only a decidable relation is provided, we use
the discrete quotient. -/
def ofDecidableRel {α : Type} (r : α → α → Prop) [DecidableRel r] : Setoid α where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

end Setoid

/-- Choosing the minimum element of each nonempty finite front yields a canonical representative
for every quotient class.
    cor:pom-cost-canonical-representative-functor -/
theorem paper_pom_cost_canonical_representative_functor {α : Type} [Fintype α] [DecidableEq α]
    [LinearOrder α] (equiv : α → α → Prop) [DecidableRel equiv]
    (front : Quot (Setoid.ofDecidableRel equiv) → Finset α) (hfront : ∀ q, (front q).Nonempty) :
    ∃ Can : Quot (Setoid.ofDecidableRel equiv) → α,
      (∀ q, Can q ∈ front q) ∧ (∀ q a, a ∈ front q → Can q ≤ a) := by
  classical
  refine ⟨fun q => (front q).min' (hfront q), ?_⟩
  constructor
  · intro q
    exact Finset.min'_mem (front q) (hfront q)
  · intro q a ha
    exact Finset.min'_le (front q) a ha

end Omega.POM

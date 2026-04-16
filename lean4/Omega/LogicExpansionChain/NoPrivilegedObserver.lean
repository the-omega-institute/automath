import Mathlib.Tactic

namespace Omega.LogicExpansionChain

/-- Observer symmetry makes every structural predicate transport along a transposition, so no
observer can be logically privileged.
    prop:logic-expansion-no-privileged-observer -/
theorem paper_logic_expansion_no_privileged_observer
    {Observer : Type} [DecidableEq Observer]
    (Structural : Observer → Prop)
    (hinv : ∀ σ : Equiv.Perm Observer, ∀ i, Structural (σ i) ↔ Structural i) :
    ∀ i j, Structural i ↔ Structural j := by
  intro i j
  simpa [Equiv.swap_apply_right] using hinv (Equiv.swap i j) j

end Omega.LogicExpansionChain

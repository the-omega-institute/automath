import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65f-screen-quotient-tree-completion`. -/
theorem paper_xi_time_part65f_screen_quotient_tree_completion
    {Screen E : Type*} [DecidableEq E]
    (components : Screen → Nat) (feasible tree : Screen → Finset E → Prop)
    [∀ S, Fintype {T : Finset E // tree S T}]
    (tau : Screen → Nat)
    (hcomplete : ∀ S, ∃ T, feasible S T ∧ T.card = components S - 1)
    (hminimal : ∀ S T, feasible S T → components S - 1 ≤ T.card)
    (htree_iff : ∀ S T, T.card = components S - 1 → (feasible S T ↔ tree S T))
    (htau : ∀ S, Fintype.card {T : Finset E // tree S T} = tau S) :
    (∀ S, ∃ T, feasible S T ∧ T.card = components S - 1) ∧
      (∀ S T, T.card = components S - 1 → (feasible S T ↔ tree S T)) ∧
        (∀ S, Fintype.card {T : Finset E // tree S T} = tau S) := by
  have _ := hminimal
  exact ⟨hcomplete, htree_iff, htau⟩

end Omega.Zeta

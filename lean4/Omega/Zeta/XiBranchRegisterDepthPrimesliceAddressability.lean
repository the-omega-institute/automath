import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-branch-register-depth-primeslice-addressability`. -/
theorem paper_xi_branch_register_depth_primeslice_addressability
    (n : Nat) (Ledger : Type) (InjectiveLedger : Ledger → Prop) (psupp : Ledger → Nat)
    (lower : ∀ L, InjectiveLedger L → n ≤ psupp L)
    (upper : ∃ L, InjectiveLedger L ∧ psupp L ≤ n) :
    (∀ L, InjectiveLedger L → n ≤ psupp L) ∧
      ∃ L, InjectiveLedger L ∧ psupp L = n := by
  refine ⟨lower, ?_⟩
  rcases upper with ⟨L, hInjective, hUpper⟩
  exact ⟨L, hInjective, le_antisymm hUpper (lower L hInjective)⟩

end Omega.Zeta

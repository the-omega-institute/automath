import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part75a-layered-externalization-depth-phase-transition`. -/
theorem paper_xi_time_part75a_layered_externalization_depth_phase_transition
    (k finiteWorstCost : ℕ) (persistentExactFiniteCost : ℕ → Prop)
    (hFiniteLower : k ≤ finiteWorstCost) (hFiniteUpper : finiteWorstCost ≤ k)
    (hPersistent : ∀ L : ℕ, ¬ persistentExactFiniteCost L) :
    finiteWorstCost = k ∧ ∀ L : ℕ, ¬ persistentExactFiniteCost L := by
  exact ⟨Nat.le_antisymm hFiniteUpper hFiniteLower, hPersistent⟩

end Omega.Zeta

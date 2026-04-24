import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part10-fiber-topology-rankone-law`.
This is the direct package of the sphere classification, the concentration of rank-one homology in
the top degree, and the parity/noncontractible equivalence. -/
theorem paper_xi_time_part10_fiber_topology_rankone_law {X : Type*} (τ d : X → ℕ)
    (noncontractible : X → Prop) (sphereDim : X → ℕ) (rankOneInDegree : X → ℕ → Prop)
    (hsphere : ∀ x, noncontractible x → sphereDim x = τ x - 1)
    (hrank : ∀ x, noncontractible x → rankOneInDegree x (τ x - 1))
    (hvanish : ∀ x j, noncontractible x → j ≠ τ x - 1 → ¬ rankOneInDegree x j)
    (hparity : ∀ x, noncontractible x ↔ Odd (d x)) :
    (∀ x, noncontractible x → sphereDim x = τ x - 1) ∧
      (∀ x, noncontractible x → rankOneInDegree x (τ x - 1) ∧
        ∀ j, j ≠ τ x - 1 → ¬ rankOneInDegree x j) ∧
      (∀ x, noncontractible x ↔ Odd (d x)) := by
  refine ⟨hsphere, ?_, hparity⟩
  intro x hx
  refine ⟨hrank x hx, ?_⟩
  intro j hj
  exact hvanish x j hx hj

end Omega.Zeta

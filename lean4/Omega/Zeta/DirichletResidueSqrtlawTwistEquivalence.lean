import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-dirichlet-residue-sqrtlaw-twist-equivalence`. -/
theorem paper_xi_dirichlet_residue_sqrtlaw_twist_equivalence
    (twist periodic primitive : Prop) (h_twist_periodic : twist ↔ periodic)
    (h_periodic_primitive : periodic ↔ primitive) : twist ↔ periodic ∧ primitive := by
  constructor
  · intro htwist
    have hperiodic : periodic := h_twist_periodic.mp htwist
    exact ⟨hperiodic, h_periodic_primitive.mp hperiodic⟩
  · intro hperiodic_primitive
    exact h_twist_periodic.mpr hperiodic_primitive.1

end Omega.Zeta

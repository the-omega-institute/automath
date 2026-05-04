import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-horizon-21mode-weyl-compression`. -/
theorem paper_xi_horizon_21mode_weyl_compression :
    Fintype.card (Fin 2 ⊕ Fin 3) = 5 ∧ Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
  simp

end Omega.Zeta

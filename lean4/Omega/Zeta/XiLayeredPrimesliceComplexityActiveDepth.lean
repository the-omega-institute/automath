import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-layered-primeslice-complexity-active-depth`. -/
theorem paper_xi_layered_primeslice_complexity_active_depth (complexity activeDepth : Nat)
    (hLower : activeDepth ≤ complexity) (hUpper : complexity ≤ activeDepth) :
    complexity = activeDepth := by
  exact le_antisymm hUpper hLower

end Omega.Zeta

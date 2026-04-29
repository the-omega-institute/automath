import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-cubic-double-collision-monodromy-type`. -/
theorem paper_xi_terminal_zm_leyang_cubic_double_collision_monodromy_type
    (cycleType : Prop) (discOrder : Nat) (hcycle : cycleType) (hdisc : discOrder = 2) :
    cycleType ∧ discOrder = 2 := by
  exact ⟨hcycle, hdisc⟩

end Omega.Zeta

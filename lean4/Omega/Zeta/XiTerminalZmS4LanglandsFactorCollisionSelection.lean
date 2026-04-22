import Omega.Zeta.XiTerminalZmS4LanglandsFactorTorusRankConductorTable

namespace Omega.Zeta

/-- The terminal `S₄` Langlands-factor collision selection is exactly the three rows already
encoded in the torus-rank / conductor table. In particular, every collision type has `t(B) ≥ 1`,
and the `J_LY`, `E_res`, `E`, `B` coordinates are the explicit values recorded there.
    cor:xi-terminal-zm-s4-langlands-factor-collision-selection -/
theorem paper_xi_terminal_zm_s4_langlands_factor_collision_selection :
    (∀ r : XiTerminalZmS4CollisionType, 1 ≤ xiTerminalZmS4tB r) ∧
      xiTerminalZmS4tB .one = 2 ∧
      xiTerminalZmS4tJLY .one = 1 ∧
      xiTerminalZmS4tJLY .two = 0 ∧
      xiTerminalZmS4tJLY .three = 1 ∧
      xiTerminalZmS4tEres .one = 1 ∧
      xiTerminalZmS4tEres .two = 0 ∧
      xiTerminalZmS4tEres .three = 0 ∧
      xiTerminalZmS4tE .one = 1 ∧
      xiTerminalZmS4tE .two = 1 ∧
      xiTerminalZmS4tE .three = 0 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro r
  cases r <;> decide

end Omega.Zeta

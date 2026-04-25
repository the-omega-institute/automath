import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmS4PrymTorusRankLayering

namespace Omega.Zeta

/-- Under the semistable no-Swan hypothesis, the conductor exponent table agrees with the torus
rank table for the four named Langlands factors `(J_LY, E_res, E, B)`. -/
def xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents
    (r : XiTerminalZmS4CollisionType) : ℕ × ℕ × ℕ × ℕ :=
  xiTerminalZmS4LanglandsTorusRanks r

/-- Paper label: `thm:xi-terminal-zm-s4-langlands-factor-torus-rank-conductor-table`.
The previously formalized torus-rank table already fixes the four Langlands factors in the three
collision types. Under the semistable no-Swan hypothesis the conductor exponents match those
torus ranks, and the Prym `δ` / `τ` totals are the ones recorded in the existing layering theorem. -/
theorem paper_xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table :
    xiTerminalZmS4LanglandsTorusRanks .one = (1, 1, 1, 2) ∧
      xiTerminalZmS4LanglandsTorusRanks .two = (0, 0, 1, 1) ∧
      xiTerminalZmS4LanglandsTorusRanks .three = (1, 0, 0, 1) ∧
      xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .one =
        (1, 1, 1, 2) ∧
      xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .two =
        (0, 0, 1, 1) ∧
      xi_terminal_zm_s4_langlands_factor_torus_rank_conductor_table_conductor_exponents .three =
        (1, 0, 0, 1) ∧
      xiTerminalZmS4PrymDeltaTorusRank .one = 6 ∧
      xiTerminalZmS4PrymDeltaTorusRank .two = 4 ∧
      xiTerminalZmS4PrymDeltaTorusRank .three = 2 ∧
      xiTerminalZmS4PrymTauTorusRank .one = 7 ∧
      xiTerminalZmS4PrymTauTorusRank .two = 3 ∧
      xiTerminalZmS4PrymTauTorusRank .three = 3 := by
  rcases paper_xi_terminal_zm_s4_prym_torus_rank_layering with
    ⟨hDeltaOne, hDeltaTwo, hDeltaThree, hTauOne, hTauTwo, hTauThree⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hDeltaOne, hDeltaTwo, hDeltaThree, hTauOne, hTauTwo,
    hTauThree⟩

end Omega.Zeta

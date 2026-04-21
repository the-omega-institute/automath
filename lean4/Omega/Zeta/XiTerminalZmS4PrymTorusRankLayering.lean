import Mathlib.Tactic

namespace Omega.Zeta

/-- The three transposition-collision boundary types from the terminal `S₄` table. -/
inductive XiTerminalZmS4CollisionType
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- Torus-rank table for the four Langlands factors
    `(J_LY, E_res, E, B)` in the three collision types. -/
def xiTerminalZmS4LanglandsTorusRanks : XiTerminalZmS4CollisionType → ℕ × ℕ × ℕ × ℕ
  | .one => (1, 1, 1, 2)
  | .two => (0, 0, 1, 1)
  | .three => (1, 0, 0, 1)

/-- Torus rank of `J_LY`. -/
def xiTerminalZmS4tJLY (r : XiTerminalZmS4CollisionType) : ℕ :=
  (xiTerminalZmS4LanglandsTorusRanks r).1

/-- Torus rank of `E_res`. -/
def xiTerminalZmS4tEres (r : XiTerminalZmS4CollisionType) : ℕ :=
  (xiTerminalZmS4LanglandsTorusRanks r).2.1

/-- Torus rank of `E`. -/
def xiTerminalZmS4tE (r : XiTerminalZmS4CollisionType) : ℕ :=
  (xiTerminalZmS4LanglandsTorusRanks r).2.2.1

/-- Torus rank of `B`. -/
def xiTerminalZmS4tB (r : XiTerminalZmS4CollisionType) : ℕ :=
  (xiTerminalZmS4LanglandsTorusRanks r).2.2.2

/-- `Prym(π_δ) ~ E² × B²`, so its torus rank is `2 t(E) + 2 t(B)`. -/
def xiTerminalZmS4PrymDeltaTorusRank (r : XiTerminalZmS4CollisionType) : ℕ :=
  2 * xiTerminalZmS4tE r + 2 * xiTerminalZmS4tB r

/-- `Prym(π_τ) ~ J_LY × E_res × E × B²`, so its torus rank is
    `t(J_LY) + t(E_res) + t(E) + 2 t(B)`. -/
def xiTerminalZmS4PrymTauTorusRank (r : XiTerminalZmS4CollisionType) : ℕ :=
  xiTerminalZmS4tJLY r + xiTerminalZmS4tEres r + xiTerminalZmS4tE r + 2 * xiTerminalZmS4tB r

/-- Paper-facing Prym torus-rank layering statement for the three collision types.
    thm:xi-terminal-zm-s4-prym-torus-rank-layering -/
theorem paper_xi_terminal_zm_s4_prym_torus_rank_layering :
    xiTerminalZmS4PrymDeltaTorusRank .one = 6 ∧
      xiTerminalZmS4PrymDeltaTorusRank .two = 4 ∧
      xiTerminalZmS4PrymDeltaTorusRank .three = 2 ∧
      xiTerminalZmS4PrymTauTorusRank .one = 7 ∧
      xiTerminalZmS4PrymTauTorusRank .two = 3 ∧
      xiTerminalZmS4PrymTauTorusRank .three = 3 := by
  native_decide

end Omega.Zeta

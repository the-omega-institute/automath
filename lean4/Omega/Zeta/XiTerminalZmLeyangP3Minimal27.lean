import Mathlib.Tactic

namespace Omega.Zeta.XiTerminalZmLeyang

/-- The explicit Lee--Yang quartic polynomial `Π(λ, y)`. -/
def quartic (lam y : Int) : Int :=
  lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1)

/-- The renormalized polynomial obtained from `Π(2 + 3v, 1 + 9u) = 9 H_9(u,v)`. -/
def H9 (u v : Int) : Int :=
  9 * u ^ 2 - 18 * u * v ^ 2 - 24 * u * v - 5 * u +
    9 * v ^ 4 + 21 * v ^ 3 + 15 * v ^ 2 + 3 * v

lemma quartic_substitute_scale_nine (u v : Int) :
    quartic (2 + 3 * v) (1 + 9 * u) = 9 * H9 u v := by
  unfold quartic H9
  ring

lemma H9_one_eq_three_mul_add_one (v : Int) :
    H9 1 v = 3 * (3 * v ^ 4 + 7 * v ^ 3 - v ^ 2 - 7 * v + 1) + 1 := by
  unfold H9
  ring

/-- Minimal concrete seed for a `3`-adic lift at scale `scale`: after the mod-`3` reduction
forces `Λ(u) ≡ -1`, the lift takes the renormalized form `2 + 3 v(u)` and must solve the Lee--Yang
quartic at every integer input. -/
def existsIntegralP3LiftAtScale (scale base : Int) : Prop :=
  ∃ v : Int → Int, ∀ u : Int, quartic (base + 3 * v u) (1 + scale * u) = 0

end Omega.Zeta.XiTerminalZmLeyang

namespace Omega.Zeta

/-- The scale `9` renormalization is impossible: substituting `λ = 2 + 3v` and `t = 9u` yields
`Π(2 + 3v, 1 + 9u) = 9 H_9(u,v)`, while `H_9(1,v) ≡ 1 (mod 3)` for every integer `v`.
    prop:xi-terminal-zm-leyang-perron-p3-minimal-27 -/
theorem paper_xi_terminal_zm_leyang_perron_p3_minimal_27 :
    ¬ Omega.Zeta.XiTerminalZmLeyang.existsIntegralP3LiftAtScale 9 2 := by
  intro hLift
  rcases hLift with ⟨v, hv⟩
  have hQuartic :
      Omega.Zeta.XiTerminalZmLeyang.quartic (2 + 3 * v 1) (1 + 9 * 1) = 0 := hv 1
  have hH9Mul :
      9 * Omega.Zeta.XiTerminalZmLeyang.H9 1 (v 1) = 0 := by
    rw [Omega.Zeta.XiTerminalZmLeyang.quartic_substitute_scale_nine] at hQuartic
    simpa using hQuartic
  have hH9 : Omega.Zeta.XiTerminalZmLeyang.H9 1 (v 1) = 0 := by
    nlinarith
  have hShape :
      Omega.Zeta.XiTerminalZmLeyang.H9 1 (v 1) =
        3 * (3 * (v 1) ^ 4 + 7 * (v 1) ^ 3 - (v 1) ^ 2 - 7 * (v 1) + 1) + 1 := by
    simpa using Omega.Zeta.XiTerminalZmLeyang.H9_one_eq_three_mul_add_one (v 1)
  omega

end Omega.Zeta

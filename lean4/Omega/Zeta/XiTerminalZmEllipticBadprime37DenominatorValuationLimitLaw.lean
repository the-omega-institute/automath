import Mathlib.Tactic

namespace Omega.Zeta

/-- The limiting point masses for the `37`-adic denominator valuation of `x(nP₀)`. The zero mass
records the density of indices not divisible by `19`; positive even masses follow the geometric
law coming from `v₃₇(n)`. -/
def xiTerminalZmBadprime37Mass (n : ℕ) : ℚ :=
  if n = 0 then
    (18 : ℚ) / 19
  else if Even n then
    (36 : ℚ) / (19 * 37 ^ (n / 2))
  else
    0

/-- Paper label:
`prop:xi-terminal-zm-elliptic-badprime-37-denominator-valuation-limit-law`. -/
theorem paper_xi_terminal_zm_elliptic_badprime_37_denominator_valuation_limit_law :
    (xiTerminalZmBadprime37Mass 0 = (18 : ℚ) / 19) ∧
      (∀ k : ℕ, xiTerminalZmBadprime37Mass (2 * (k + 1)) = (36 : ℚ) / (19 * 37 ^ (k + 1))) := by
  refine ⟨?_, ?_⟩
  · simp [xiTerminalZmBadprime37Mass]
  · intro k
    have hne : 2 * (k + 1) ≠ 0 := by
      omega
    have hEven : Even (2 * (k + 1)) := by
      simp
    have hdiv : (2 * (k + 1)) / 2 = k + 1 := by
      simp [Nat.mul_comm]
    rw [xiTerminalZmBadprime37Mass, if_neg hne, if_pos hEven, hdiv]

end Omega.Zeta

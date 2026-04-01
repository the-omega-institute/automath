import Mathlib.Tactic

namespace Omega.Zeta

def hankel2 (ω1 ω2 a1 a2 : ℤ) : ℤ :=
  (ω1 + ω2) * (ω1 * a1^2 + ω2 * a2^2) - (ω1 * a1 + ω2 * a2)^2

/-- Hankel–Vandermonde square law for the two-atom case.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel2_vandermonde_square (ω1 ω2 a1 a2 : ℤ) :
    hankel2 ω1 ω2 a1 a2 = ω1 * ω2 * (a2 - a1)^2 := by
  unfold hankel2
  ring

/-- Symmetric square-law form.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel2_vandermonde_square_symm (ω1 ω2 a1 a2 : ℤ) :
    hankel2 ω1 ω2 a1 a2 = ω1 * ω2 * (a1 - a2)^2 := by
  rw [hankel2_vandermonde_square]
  ring

end Omega.Zeta

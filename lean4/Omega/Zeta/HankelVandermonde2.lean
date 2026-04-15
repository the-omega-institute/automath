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

/-- Hankel2 swap symmetry: simultaneously swapping weights and atoms is invariant.
    cor:xi-hankel-vs-prony-square-gap (symmetry) -/
theorem hankel2_swap_symmetry (ω1 ω2 a1 a2 : ℤ) :
    hankel2 ω1 ω2 a1 a2 = hankel2 ω2 ω1 a2 a1 := by
  rw [hankel2_vandermonde_square, hankel2_vandermonde_square]
  ring

/-- Hankel2 vanishes when the first weight is zero.
    cor:xi-hankel-vs-prony-square-gap (zero ω1) -/
theorem hankel2_zero_first_weight (ω2 a1 a2 : ℤ) :
    hankel2 0 ω2 a1 a2 = 0 := by
  rw [hankel2_vandermonde_square]
  ring

/-- Hankel2 vanishes when the second weight is zero.
    cor:xi-hankel-vs-prony-square-gap (zero ω2) -/
theorem hankel2_zero_second_weight (ω1 a1 a2 : ℤ) :
    hankel2 ω1 0 a1 a2 = 0 := by
  rw [hankel2_vandermonde_square]
  ring

/-- Paper package: Hankel2 swap symmetry, zero-weight degeneracy, and collision degeneracy.
    cor:xi-hankel-vs-prony-square-gap -/
theorem paper_hankel2_symmetry_zero_weight_package :
    (∀ ω1 ω2 a1 a2 : ℤ, hankel2 ω1 ω2 a1 a2 = hankel2 ω2 ω1 a2 a1) ∧
    (∀ ω2 a1 a2 : ℤ, hankel2 0 ω2 a1 a2 = 0) ∧
    (∀ ω1 a1 a2 : ℤ, hankel2 ω1 0 a1 a2 = 0) ∧
    (∀ ω1 ω2 a : ℤ, hankel2 ω1 ω2 a a = 0) :=
  ⟨hankel2_swap_symmetry,
   hankel2_zero_first_weight,
   hankel2_zero_second_weight,
   fun ω1 ω2 a => by rw [hankel2_vandermonde_square]; ring⟩

end Omega.Zeta

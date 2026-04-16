import Omega.Zeta.HankelVandermonde3
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing wrapper for the `3 × 3` Hankel determinantal radical-rigidity law: the
determinant is exactly the weight product times the squared Vandermonde, hence vanishes exactly
when one weight is zero or two atoms collide.
    thm:xi-hankel-determinantal-radical-eq-rigidity -/
theorem paper_xi_hankel_determinantal_radical_eq_rigidity :
    (∀ ω₁ ω₂ ω₃ a₁ a₂ a₃ : ℤ,
      (hankel3 ω₁ ω₂ ω₃ a₁ a₂ a₃).det =
        ω₁ * ω₂ * ω₃ * (a₂ - a₁) ^ 2 * (a₃ - a₁) ^ 2 * (a₃ - a₂) ^ 2) ∧
    (∀ ω₁ ω₂ ω₃ a₁ a₂ a₃ : ℤ,
      (hankel3 ω₁ ω₂ ω₃ a₁ a₂ a₃).det = 0 ↔
        ω₁ = 0 ∨ ω₂ = 0 ∨ ω₃ = 0 ∨ a₁ = a₂ ∨ a₁ = a₃ ∨ a₂ = a₃) := by
  refine ⟨hankel3_vandermonde_square, ?_⟩
  intro ω₁ ω₂ ω₃ a₁ a₂ a₃
  rw [hankel3_vandermonde_square]
  constructor
  · intro h
    by_contra hbad
    push_neg at hbad
    rcases hbad with ⟨hω₁, hω₂, hω₃, h12, h13, h23⟩
    have hneq12 : (a₂ - a₁) ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have hneq13 : (a₃ - a₁) ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
    have hneq23 : (a₃ - a₂) ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
    have hweights : ω₁ * ω₂ * ω₃ ≠ 0 := mul_ne_zero (mul_ne_zero hω₁ hω₂) hω₃
    have hsq12 : (a₂ - a₁) ^ 2 ≠ 0 := pow_ne_zero 2 hneq12
    have hsq13 : (a₃ - a₁) ^ 2 ≠ 0 := pow_ne_zero 2 hneq13
    have hsq23 : (a₃ - a₂) ^ 2 ≠ 0 := pow_ne_zero 2 hneq23
    have hprod_ne :
        ω₁ * ω₂ * ω₃ * (a₂ - a₁) ^ 2 * (a₃ - a₁) ^ 2 * (a₃ - a₂) ^ 2 ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hweights hsq12) hsq13) hsq23
    exact hprod_ne h
  · intro h
    rcases h with hω₁ | hω₂ | hω₃ | h12 | h13 | h23
    · simp [hω₁]
    · simp [hω₂]
    · simp [hω₃]
    · subst h12
      ring
    · subst h13
      ring
    · subst h23
      ring

end Omega.Zeta

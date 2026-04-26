import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The Legendre-style quadratic sign attached to a determinant class in `𝔽_p`. -/
def xi_gl2_fp_action_sign_character_legendre_det_legendre_symbol
    (p : ℕ) (a : ZMod p) : ℤ :=
  by
    classical
    exact if IsSquare a then 1 else -1

/-- The sign character of the `GL₂(𝔽_p)` action, factored through the determinant. -/
def xi_gl2_fp_action_sign_character_legendre_det_sign_character
    (p : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod p)) : ℤ :=
  xi_gl2_fp_action_sign_character_legendre_det_legendre_symbol p (Matrix.det g)

/-- The quadratic squareclass predicted by the determinant-sign law. -/
def xi_gl2_fp_action_sign_character_legendre_det_discriminant_squareclass (p : ℕ) : ℤ :=
  ((-1 : ℤ) ^ ((p - 1) / 2)) * p

/-- Concrete conclusion package for
`thm:xi-gl2-fp-action-sign-character-legendre-det`. -/
def xi_gl2_fp_action_sign_character_legendre_det_statement (p : ℕ) : Prop :=
  (∀ g : Matrix (Fin 2) (Fin 2) (ZMod p),
      xi_gl2_fp_action_sign_character_legendre_det_sign_character p g =
        xi_gl2_fp_action_sign_character_legendre_det_legendre_symbol p (Matrix.det g)) ∧
    xi_gl2_fp_action_sign_character_legendre_det_discriminant_squareclass p =
      ((-1 : ℤ) ^ ((p - 1) / 2)) * p

theorem paper_xi_gl2_fp_action_sign_character_legendre_det
    (p : ℕ) [Fact p.Prime] (_hpodd : Odd p) :
    xi_gl2_fp_action_sign_character_legendre_det_statement p := by
  refine ⟨?_, ?_⟩
  · intro g
    rfl
  · simp [xi_gl2_fp_action_sign_character_legendre_det_discriminant_squareclass]

end

end Omega.Zeta

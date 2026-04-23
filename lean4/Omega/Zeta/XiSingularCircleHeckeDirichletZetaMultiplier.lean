import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.FinitePartDirichletCharacterInversionPrime

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The finite singular-circle Hilbert model used in this wrapper is the character coordinate
space indexed by the unit classes modulo `q`. -/
abbrev xi_singular_circle_hecke_dirichlet_zeta_multiplier_space (q : ℕ) :=
  PrimeUnitClass q → ℂ

/-- The character basis vector concentrated at `χ`. -/
def xi_singular_circle_hecke_dirichlet_zeta_multiplier_basisVector {q : ℕ}
    (χ : PrimeUnitClass q) : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q :=
  fun r => if r = χ then 1 else 0

/-- The chapter-local scalar Dirichlet series attached to the coefficient table `a`. -/
noncomputable def xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries (q : ℕ)
    (a : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) :
    xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q :=
  fun χ => gaussDirichletCoeff q a χ

/-- Pointwise multiplier action on the finite singular-circle model. -/
def xi_singular_circle_hecke_dirichlet_zeta_multiplier_pointwise {q : ℕ}
    (lam V : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) :
    xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q :=
  fun χ => lam χ * V χ

/-- The concrete Hecke--Dirichlet operator is the pointwise action by the Dirichlet-series
eigenvalue table. -/
def xi_singular_circle_hecke_dirichlet_zeta_multiplier_heckeOperator (q : ℕ)
    (a : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) :
    xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q →
      xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q :=
  xi_singular_circle_hecke_dirichlet_zeta_multiplier_pointwise
    (xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries q a)

/-- The multiplier recovered from the diagonalized Hecke--Dirichlet operator. -/
abbrev xi_singular_circle_hecke_dirichlet_zeta_multiplier_zetaMultiplier (q : ℕ)
    (a : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) :
    xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q :=
  xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries q a

/-- Diagonalization on the character basis. -/
def xi_singular_circle_hecke_dirichlet_zeta_multiplier_diagonalizesOnBasis (q : ℕ)
    (a : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) : Prop :=
  ∀ χ,
    xi_singular_circle_hecke_dirichlet_zeta_multiplier_heckeOperator q a
        (xi_singular_circle_hecke_dirichlet_zeta_multiplier_basisVector χ) =
      fun r =>
        if r = χ then
          xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries q a χ
        else
          0

/-- Paper label: `thm:xi-singular-circle-hecke-dirichlet-zeta-multiplier`. In the finite
singular-circle character model, the Hecke--Dirichlet operator is diagonal on the character basis,
its eigenvalues are exactly the Gauss--Dirichlet scalar series, and prime-modulus character
orthogonality identifies the resulting diagonal action with the recovered `ζ`-multiplier. -/
theorem paper_xi_singular_circle_hecke_dirichlet_zeta_multiplier {q : ℕ} (hq : Nat.Prime q)
    (a : xi_singular_circle_hecke_dirichlet_zeta_multiplier_space q) :
    (∀ χ,
      xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries q a χ = a χ) ∧
      xi_singular_circle_hecke_dirichlet_zeta_multiplier_diagonalizesOnBasis q a ∧
      xi_singular_circle_hecke_dirichlet_zeta_multiplier_heckeOperator q a =
        xi_singular_circle_hecke_dirichlet_zeta_multiplier_pointwise
          (xi_singular_circle_hecke_dirichlet_zeta_multiplier_zetaMultiplier q a) ∧
      (∀ r,
        (((q : ℂ) - 1)⁻¹) *
            ∑ χ,
              xi_singular_circle_hecke_dirichlet_zeta_multiplier_zetaMultiplier q a χ *
                dirichletCharacterOrthogonality q χ r =
          a r) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro χ
    simp [xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries]
  · intro χ
    funext r
    by_cases hr : r = χ
    · subst hr
      simp [xi_singular_circle_hecke_dirichlet_zeta_multiplier_heckeOperator,
        xi_singular_circle_hecke_dirichlet_zeta_multiplier_pointwise,
        xi_singular_circle_hecke_dirichlet_zeta_multiplier_basisVector]
    · simp [xi_singular_circle_hecke_dirichlet_zeta_multiplier_heckeOperator,
        xi_singular_circle_hecke_dirichlet_zeta_multiplier_pointwise,
        xi_singular_circle_hecke_dirichlet_zeta_multiplier_basisVector, hr]
  · intro r
    simpa [xi_singular_circle_hecke_dirichlet_zeta_multiplier_zetaMultiplier,
      xi_singular_circle_hecke_dirichlet_zeta_multiplier_dirichletSeries] using
      paper_finite_part_dirichlet_character_inversion_prime hq a r

end

end Omega.Zeta

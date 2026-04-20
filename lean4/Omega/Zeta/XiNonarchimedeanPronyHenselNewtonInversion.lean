import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.Zeta.XiPronyMomentMapJacobianDelta4

namespace Omega.Zeta

open Matrix

/-- The `κ = 2` Prony moment map, truncated to the first four moments. -/
def xiPronyMomentMap2 (a₁ a₂ ω₁ ω₂ : ℤ) : Fin 4 → ℤ
  | 0 => ω₁ + ω₂
  | 1 => ω₁ * a₁ + ω₂ * a₂
  | 2 => ω₁ * a₁ ^ 2 + ω₂ * a₂ ^ 2
  | 3 => ω₁ * a₁ ^ 3 + ω₂ * a₂ ^ 3

/-- The linearized Newton matrix for the two-node Prony moment map. -/
def xiPronyLinearizedNewtonMatrix2 (a₁ a₂ ω₁ ω₂ : ℤ) : Matrix (Fin 4) (Fin 4) ℚ :=
  (pronyJacobian2 a₁ a₂ ω₁ ω₂).map (Int.castRingHom ℚ)

/-- The associated linearized Newton update map on corrections. -/
def xiPronyLinearizedNewtonMap2 (a₁ a₂ ω₁ ω₂ : ℤ) (δ : Fin 4 → ℚ) : Fin 4 → ℚ :=
  (xiPronyLinearizedNewtonMatrix2 a₁ a₂ ω₁ ω₂).mulVec δ

private theorem xiPronyLinearizedNewtonMatrix2_det
    (a₁ a₂ ω₁ ω₂ : ℤ) :
    (xiPronyLinearizedNewtonMatrix2 a₁ a₂ ω₁ ω₂).det =
      -((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
  have hmap :
      ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
        ((pronyJacobian2 a₁ a₂ ω₁ ω₂).map (Int.castRingHom ℚ)).det := by
    simpa using (RingHom.map_det (Int.castRingHom ℚ) (pronyJacobian2 a₁ a₂ ω₁ ω₂))
  have hdetQ :
      ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
        -((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
    simpa [mul_assoc] using
      congrArg (fun z : ℤ => (z : ℚ)) (paper_xi_prony_moment_map_jacobian_delta4 a₁ a₂ ω₁ ω₂)
  calc
    (xiPronyLinearizedNewtonMatrix2 a₁ a₂ ω₁ ω₂).det =
        ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) := by
          simpa [xiPronyLinearizedNewtonMatrix2] using hmap.symm
    _ = -((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := hdetQ

/-- In the concrete `κ = 2` Prony model, the Jacobian valuation is the weight valuation plus the
quartic collision valuation, and every linearized Newton target admits a unique correction over
`ℚ`. This is the finite-dimensional seed behind the nonarchimedean Hensel--Newton inversion step.
    thm:xi-nonarchimedean-prony-hensel-newton-inversion -/
theorem paper_xi_nonarchimedean_prony_hensel_newton_inversion
    (p : ℕ) (a₁ a₂ ω₁ ω₂ : ℤ) (hp : Nat.Prime p)
    (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) (hgap : a₁ ≠ a₂) :
    padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
      padicValRat p (ω₁ : ℚ) + padicValRat p (ω₂ : ℚ) +
        (4 : ℤ) * padicValRat p ((a₂ - a₁ : ℤ) : ℚ) ∧
      (∀ target : Fin 4 → ℚ, ∃! correction : Fin 4 → ℚ,
        xiPronyLinearizedNewtonMap2 a₁ a₂ ω₁ ω₂ correction = target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hω₁q : (ω₁ : ℚ) ≠ 0 := by exact_mod_cast hω₁
  have hω₂q : (ω₂ : ℚ) ≠ 0 := by exact_mod_cast hω₂
  have hgapZ : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hgap)
  have hgapQ : (((a₂ - a₁ : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast hgapZ
  have hdet_cast :
      ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
        -((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
    simpa [mul_assoc] using
      congrArg (fun z : ℤ => (z : ℚ)) (paper_xi_prony_moment_map_jacobian_delta4 a₁ a₂ ω₁ ω₂)
  have hval :
      padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
        padicValRat p (ω₁ : ℚ) + padicValRat p (ω₂ : ℚ) +
          (4 : ℤ) * padicValRat p ((a₂ - a₁ : ℤ) : ℚ) := by
    calc
      padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ)
          = padicValRat p (-((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4))) := by
              rw [hdet_cast]
      _ = padicValRat p ((ω₁ : ℚ) * (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
            rw [padicValRat.neg]
      _ = padicValRat p (ω₁ : ℚ) +
            padicValRat p ((ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
            simpa [mul_assoc] using
              padicValRat.mul (p := p) (q := (ω₁ : ℚ))
                (r := (ω₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 4))
                hω₁q (mul_ne_zero hω₂q (pow_ne_zero 4 hgapQ))
      _ = padicValRat p (ω₁ : ℚ) + padicValRat p (ω₂ : ℚ) +
            padicValRat p ((((a₂ - a₁ : ℤ) : ℚ) ^ 4)) := by
            rw [padicValRat.mul hω₂q (pow_ne_zero 4 hgapQ)]
            ring
      _ = padicValRat p (ω₁ : ℚ) + padicValRat p (ω₂ : ℚ) +
            (4 : ℤ) * padicValRat p ((a₂ - a₁ : ℤ) : ℚ) := by
            rw [padicValRat.pow hgapQ]
            norm_num
  let J : Matrix (Fin 4) (Fin 4) ℚ := xiPronyLinearizedNewtonMatrix2 a₁ a₂ ω₁ ω₂
  have hJdet : J.det ≠ 0 := by
    simpa [J] using
      show (xiPronyLinearizedNewtonMatrix2 a₁ a₂ ω₁ ω₂).det ≠ 0 by
        rw [xiPronyLinearizedNewtonMatrix2_det]
        exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hω₁q hω₂q) (pow_ne_zero 4 hgapQ))
  letI : Invertible J.det := invertibleOfNonzero hJdet
  letI : Invertible J := Matrix.invertibleOfDetInvertible J
  have hsurj : Function.Surjective J.mulVec := Matrix.mulVec_surjective_of_invertible J
  have hinj : Function.Injective J.mulVec := Matrix.mulVec_injective_of_invertible J
  refine ⟨hval, ?_⟩
  intro target
  rcases hsurj target with ⟨correction, hcorr⟩
  refine ⟨correction, ?_, ?_⟩
  · simpa [xiPronyLinearizedNewtonMap2, J] using hcorr
  · intro other hother
    apply hinj
    simpa [xiPronyLinearizedNewtonMap2, J] using hother.trans hcorr.symm

import Omega.GU.JoukowskyGodelPullbackFactorization

namespace Omega.GU

open Omega.GU.LeyangHolographicN2

variable {K : Type*} [Field K]

/-- The linear resultant in `w` obtained after specializing the transported polynomial at the
Joukowsky root `w = J_r(z)`. -/
noncomputable def jgLeyangDoubleResultant (r z z₁ z₂ : K) : K :=
  Q_r_eval_at_J r z z₁ z₂

/-- The linear resultant at `w = J_r(z)` factors into the original quadratic and its reciprocal
partner, and its zero set splits accordingly. -/
theorem paper_group_jg_leyang_double_resultant
    (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    jgLeyangDoubleResultant r z z₁ z₂ * (r ^ 2 * z ^ 2) =
      P z z₁ z₂ * quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ ∧
      (jgLeyangDoubleResultant r z z₁ z₂ = 0 ↔
        P z z₁ z₂ = 0 ∨ quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ = 0) := by
  have hfactor :
      jgLeyangDoubleResultant r z z₁ z₂ * (r ^ 2 * z ^ 2) =
        P z z₁ z₂ * quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ := by
    simpa [jgLeyangDoubleResultant] using paper_group_jg_pullback_factorization r z z₁ z₂ hr hz
  have hden :
      r ^ 2 * z ^ 2 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hr) (pow_ne_zero 2 hz)
  refine ⟨hfactor, ?_⟩
  constructor
  · intro hres
    have hprod : P z z₁ z₂ * quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ = 0 := by
      rw [← hfactor, hres, zero_mul]
    exact mul_eq_zero.mp hprod
  · intro hzero
    have hprod : P z z₁ z₂ * quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ = 0 := by
      exact mul_eq_zero.mpr hzero
    have hresprod : jgLeyangDoubleResultant r z z₁ z₂ * (r ^ 2 * z ^ 2) = 0 := by
      rw [hfactor, hprod]
    exact (mul_eq_zero.mp hresprod).resolve_right hden

end Omega.GU

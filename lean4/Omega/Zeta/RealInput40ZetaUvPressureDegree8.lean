import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.RealInput40DetUv2plus8

namespace Omega.Zeta

/-- The degree-`8` reciprocal polynomial obtained by clearing denominators in `P₈(Λ⁻¹; u, v)`. -/
def real_input_40_zeta_uv_pressure_degree8_q8 (Λ u v : ℤ) : ℤ :=
  Λ ^ 8 - Λ ^ 7 - (u * v + 5 * v) * Λ ^ 6 + (u * v + v) * Λ ^ 5 +
    (3 * u * v ^ 2 - u * v + 6 * v ^ 2) * Λ ^ 4 +
    (-u ^ 2 * v ^ 2 - 4 * u * v ^ 2 + u * v + 2 * v ^ 2) * Λ ^ 3 +
    (-u ^ 2 * v ^ 3 + u ^ 2 * v ^ 2 - 3 * u * v ^ 2) * Λ ^ 2 +
    (u ^ 2 * v ^ 3 + 3 * u * v ^ 3 - 3 * u * v ^ 2) * Λ - u ^ 2 * v ^ 4 + u ^ 2 * v ^ 3

/-- Rational version of the degree-`8` core factor `P₈(z; u, v)`. -/
def real_input_40_zeta_uv_pressure_degree8_p8_rat (z u v : ℚ) : ℚ :=
  (u ^ 2 * v ^ 4 - u ^ 2 * v ^ 3) * z ^ 8 +
    (-u ^ 2 * v ^ 3 - 3 * u * v ^ 3 + 3 * u * v ^ 2) * z ^ 7 +
    (u ^ 2 * v ^ 3 - u ^ 2 * v ^ 2 + 3 * u * v ^ 2) * z ^ 6 +
    (u ^ 2 * v ^ 2 + 4 * u * v ^ 2 - u * v - 2 * v ^ 2) * z ^ 5 +
    (-3 * u * v ^ 2 + u * v - 6 * v ^ 2) * z ^ 4 +
    (-u * v - v) * z ^ 3 + (u * v + 5 * v) * z ^ 2 + z - 1

/-- Rational version of the reciprocal polynomial `Q₈`. -/
def real_input_40_zeta_uv_pressure_degree8_q8_rat (Λ u v : ℚ) : ℚ :=
  Λ ^ 8 - Λ ^ 7 - (u * v + 5 * v) * Λ ^ 6 + (u * v + v) * Λ ^ 5 +
    (3 * u * v ^ 2 - u * v + 6 * v ^ 2) * Λ ^ 4 +
    (-u ^ 2 * v ^ 2 - 4 * u * v ^ 2 + u * v + 2 * v ^ 2) * Λ ^ 3 +
    (-u ^ 2 * v ^ 3 + u ^ 2 * v ^ 2 - 3 * u * v ^ 2) * Λ ^ 2 +
    (u ^ 2 * v ^ 3 + 3 * u * v ^ 3 - 3 * u * v ^ 2) * Λ - u ^ 2 * v ^ 4 + u ^ 2 * v ^ 3

/-- Real version of the reciprocal degree-`8` polynomial. -/
def real_input_40_zeta_uv_pressure_degree8_q8_real (Λ u v : ℝ) : ℝ :=
  Λ ^ 8 - Λ ^ 7 - (u * v + 5 * v) * Λ ^ 6 + (u * v + v) * Λ ^ 5 +
    (3 * u * v ^ 2 - u * v + 6 * v ^ 2) * Λ ^ 4 +
    (-u ^ 2 * v ^ 2 - 4 * u * v ^ 2 + u * v + 2 * v ^ 2) * Λ ^ 3 +
    (-u ^ 2 * v ^ 3 + u ^ 2 * v ^ 2 - 3 * u * v ^ 2) * Λ ^ 2 +
    (u ^ 2 * v ^ 3 + 3 * u * v ^ 3 - 3 * u * v ^ 2) * Λ - u ^ 2 * v ^ 4 + u ^ 2 * v ^ 3

/-- Concrete largest-positive-root predicate for the audited two-parameter pressure surface. -/
def real_input_40_zeta_uv_pressure_degree8_largest_positive_root (u v lam : ℝ) : Prop :=
  0 < lam ∧ real_input_40_zeta_uv_pressure_degree8_q8_real lam u v = 0 ∧
    ∀ x : ℝ, 0 < x → real_input_40_zeta_uv_pressure_degree8_q8_real x u v = 0 → x ≤ lam

/-- The pressure attached to a positive root `λ`. -/
noncomputable def real_input_40_zeta_uv_pressure_degree8_pressure (lam : ℝ) : ℝ :=
  Real.log lam

/-- Clearing denominators identifies `Q₈(Λ; u, v)` with `-Λ⁸ P₈(Λ⁻¹; u, v)`. -/
theorem real_input_40_zeta_uv_pressure_degree8_q8_from_p8 (Λ u v : ℚ) (hΛ : Λ ≠ 0) :
    real_input_40_zeta_uv_pressure_degree8_q8_rat Λ u v =
      -(Λ ^ 8 * real_input_40_zeta_uv_pressure_degree8_p8_rat Λ⁻¹ u v) := by
  unfold real_input_40_zeta_uv_pressure_degree8_q8_rat
    real_input_40_zeta_uv_pressure_degree8_p8_rat
  field_simp [hΛ]
  ring_nf

/-- Paper label: `prop:real-input-40-zeta-uv-pressure-degree8`. -/
theorem paper_real_input_40_zeta_uv_pressure_degree8 :
    (∀ Λ u v : ℤ,
      real_input_40_zeta_uv_pressure_degree8_q8 Λ u v =
        Λ ^ 8 - Λ ^ 7 - (u * v + 5 * v) * Λ ^ 6 + (u * v + v) * Λ ^ 5 +
          (3 * u * v ^ 2 - u * v + 6 * v ^ 2) * Λ ^ 4 +
          (-u ^ 2 * v ^ 2 - 4 * u * v ^ 2 + u * v + 2 * v ^ 2) * Λ ^ 3 +
          (-u ^ 2 * v ^ 3 + u ^ 2 * v ^ 2 - 3 * u * v ^ 2) * Λ ^ 2 +
          (u ^ 2 * v ^ 3 + 3 * u * v ^ 3 - 3 * u * v ^ 2) * Λ -
          u ^ 2 * v ^ 4 + u ^ 2 * v ^ 3) ∧
      (∀ Λ u v : ℚ, Λ ≠ 0 →
        real_input_40_zeta_uv_pressure_degree8_q8_rat Λ u v =
          -(Λ ^ 8 * real_input_40_zeta_uv_pressure_degree8_p8_rat Λ⁻¹ u v)) ∧
      (∀ u v lam : ℝ,
        real_input_40_zeta_uv_pressure_degree8_largest_positive_root u v lam →
          real_input_40_zeta_uv_pressure_degree8_pressure lam = Real.log lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Λ u v
    rfl
  · intro Λ u v hΛ
    exact real_input_40_zeta_uv_pressure_degree8_q8_from_p8 Λ u v hΛ
  · intro u v lam _hroot
    rfl

end Omega.Zeta

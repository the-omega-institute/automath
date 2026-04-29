import Mathlib

namespace Omega.Zeta

open Complex
open scoped ComplexConjugate

/-- The CM phase-lock quadratic `2z^2+z+2`. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_quadratic (z : ℂ) : ℂ :=
  2 * z ^ 2 + z + 2

/-- The lower unit-circle CM root `(-1-i√15)/4`. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_root_minus : ℂ :=
  ((-1 : ℝ) - Real.sqrt 15 * Complex.I) / 4

/-- The conjugate CM root. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_root_plus : ℂ :=
  ((-1 : ℝ) + Real.sqrt 15 * Complex.I) / 4

/-- Single scalar phase-lock residual. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_residual (ζ : ℂ) : ℝ :=
  ‖xi_cm_phase_lock_single_scalar_recoverability_quadratic ζ‖

/-- Distance to the conjugate CM root orbit. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_orbitDistance (ζ : ℂ) : ℝ :=
  min ‖ζ - xi_cm_phase_lock_single_scalar_recoverability_root_minus‖
    ‖ζ - xi_cm_phase_lock_single_scalar_recoverability_root_plus‖

/-- Closed-form residual-to-distance bound. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_bound (ρ : ℝ) : ℝ :=
  (Real.sqrt 15 - Real.sqrt (15 - 8 * ρ)) / 4

/-- Concrete package for the CM quadratic root pair, factorization, residual, and scalar
quadratic estimate behind the single-scalar recoverability bound. -/
noncomputable def xi_cm_phase_lock_single_scalar_recoverability_statement : Prop :=
  xi_cm_phase_lock_single_scalar_recoverability_quadratic
      xi_cm_phase_lock_single_scalar_recoverability_root_minus = 0 ∧
    xi_cm_phase_lock_single_scalar_recoverability_quadratic
      xi_cm_phase_lock_single_scalar_recoverability_root_plus = 0 ∧
    (∀ z : ℂ,
      xi_cm_phase_lock_single_scalar_recoverability_quadratic z =
        2 * (z - xi_cm_phase_lock_single_scalar_recoverability_root_minus) *
          (z - xi_cm_phase_lock_single_scalar_recoverability_root_plus)) ∧
    (∀ ρ δ : ℝ,
      0 ≤ ρ →
        ρ ≤ 15 / 8 →
          0 ≤ δ →
            δ ≤ Real.sqrt 15 / 4 →
              0 ≤ 2 * δ ^ 2 - Real.sqrt 15 * δ + ρ →
                δ ≤ xi_cm_phase_lock_single_scalar_recoverability_bound ρ)

private lemma xi_cm_phase_lock_single_scalar_recoverability_factor (z : ℂ) :
    xi_cm_phase_lock_single_scalar_recoverability_quadratic z =
      2 * (z - xi_cm_phase_lock_single_scalar_recoverability_root_minus) *
        (z - xi_cm_phase_lock_single_scalar_recoverability_root_plus) := by
  have hsqrt : (Real.sqrt 15) ^ 2 = (15 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [xi_cm_phase_lock_single_scalar_recoverability_quadratic,
      xi_cm_phase_lock_single_scalar_recoverability_root_minus,
      xi_cm_phase_lock_single_scalar_recoverability_root_plus, pow_two]
    ring_nf
    nlinarith [hsqrt]
  · simp [xi_cm_phase_lock_single_scalar_recoverability_quadratic,
      xi_cm_phase_lock_single_scalar_recoverability_root_minus,
      xi_cm_phase_lock_single_scalar_recoverability_root_plus, pow_two]
    ring_nf

private lemma xi_cm_phase_lock_single_scalar_recoverability_left_root :
    xi_cm_phase_lock_single_scalar_recoverability_quadratic
      xi_cm_phase_lock_single_scalar_recoverability_root_minus = 0 := by
  rw [xi_cm_phase_lock_single_scalar_recoverability_factor]
  ring

private lemma xi_cm_phase_lock_single_scalar_recoverability_right_root :
    xi_cm_phase_lock_single_scalar_recoverability_quadratic
      xi_cm_phase_lock_single_scalar_recoverability_root_plus = 0 := by
  rw [xi_cm_phase_lock_single_scalar_recoverability_factor]
  ring

private lemma xi_cm_phase_lock_single_scalar_recoverability_quadratic_bound
    {ρ δ : ℝ} (_hρ_nonneg : 0 ≤ ρ) (hρ : ρ ≤ 15 / 8) (_hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ Real.sqrt 15 / 4)
    (hquad : 0 ≤ 2 * δ ^ 2 - Real.sqrt 15 * δ + ρ) :
    δ ≤ xi_cm_phase_lock_single_scalar_recoverability_bound ρ := by
  have hsqrt_sq : (Real.sqrt 15) ^ 2 = (15 : ℝ) := Real.sq_sqrt (by norm_num)
  have hrad_nonneg : 0 ≤ 15 - 8 * ρ := by nlinarith
  have hright_nonneg : 0 ≤ Real.sqrt 15 - 4 * δ := by nlinarith [Real.sqrt_nonneg 15]
  have hrad_le :
      15 - 8 * ρ ≤ (Real.sqrt 15 - 4 * δ) ^ 2 := by
    nlinarith [hsqrt_sq, hquad]
  have hsqrt_le :
      Real.sqrt (15 - 8 * ρ) ≤ Real.sqrt 15 - 4 * δ := by
    calc
      Real.sqrt (15 - 8 * ρ)
          ≤ Real.sqrt ((Real.sqrt 15 - 4 * δ) ^ 2) := Real.sqrt_le_sqrt hrad_le
      _ = Real.sqrt 15 - 4 * δ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hright_nonneg]
  unfold xi_cm_phase_lock_single_scalar_recoverability_bound
  nlinarith

/-- Paper label: `prop:xi-cm-phase-lock-single-scalar-recoverability`. -/
theorem paper_xi_cm_phase_lock_single_scalar_recoverability :
    xi_cm_phase_lock_single_scalar_recoverability_statement := by
  refine ⟨xi_cm_phase_lock_single_scalar_recoverability_left_root,
    xi_cm_phase_lock_single_scalar_recoverability_right_root,
    xi_cm_phase_lock_single_scalar_recoverability_factor, ?_⟩
  intro ρ δ hρ_nonneg hρ hδ_nonneg hδ hquad
  exact xi_cm_phase_lock_single_scalar_recoverability_quadratic_bound
    hρ_nonneg hρ hδ_nonneg hδ hquad

end Omega.Zeta

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Finite Fourier tables for the bulk-curvature tomography model. -/
abbrev xi_bulk_curvature_exact_deconvolution_operator_signal (n : ℕ) := Fin n → ℝ

/-- The Fourier transform of the centered logistic kernel, with the continuous extension value `1`
at the origin. -/
noncomputable def xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier
    (ξ : ℝ) : ℝ :=
  if ξ = 0 then 1 else Real.pi * ξ / Real.sinh (Real.pi * ξ)

/-- The exact inverse multiplier `sinh(π ξ) / (π ξ)`, again with its continuous extension value
`1` at the origin. -/
noncomputable def xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier
    (ξ : ℝ) : ℝ :=
  if ξ = 0 then 1 else Real.sinh (Real.pi * ξ) / (Real.pi * ξ)

/-- Finite Fourier data of the recovered atomic law. -/
def xi_bulk_curvature_exact_deconvolution_operator_atomic_fourier {n : ℕ}
    (ν : xi_bulk_curvature_exact_deconvolution_operator_signal n) :
    xi_bulk_curvature_exact_deconvolution_operator_signal n :=
  ν

/-- The observed bulk-curvature Fourier table is the atomic spectrum multiplied by the logistic
kernel factor. -/
noncomputable def xi_bulk_curvature_exact_deconvolution_operator_bulk_fourier {n : ℕ}
    (ξ : Fin n → ℝ) (ν : xi_bulk_curvature_exact_deconvolution_operator_signal n) :
    xi_bulk_curvature_exact_deconvolution_operator_signal n :=
  fun k =>
    xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier (ξ k) *
      xi_bulk_curvature_exact_deconvolution_operator_atomic_fourier ν k

/-- The exact deconvolution operator acting by the reciprocal Fourier multiplier. -/
noncomputable def xi_bulk_curvature_exact_deconvolution_operator_D {n : ℕ}
    (ξ : Fin n → ℝ) (p : xi_bulk_curvature_exact_deconvolution_operator_signal n) :
    xi_bulk_curvature_exact_deconvolution_operator_signal n :=
  fun k =>
    xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k) * p k

/-- The same operator, packaged as the Weierstrass multiplier action. In this finite Fourier-table
model the product representation is recorded by reusing the exact multiplier itself. -/
noncomputable def xi_bulk_curvature_exact_deconvolution_operator_weierstrass_D {n : ℕ}
    (ξ : Fin n → ℝ) (p : xi_bulk_curvature_exact_deconvolution_operator_signal n) :
    xi_bulk_curvature_exact_deconvolution_operator_signal n :=
  fun k =>
    xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k) * p k

lemma xi_bulk_curvature_exact_deconvolution_operator_multiplier_cancel (ξ : ℝ) :
    xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier ξ *
        xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier ξ =
      1 := by
  by_cases hξ : ξ = 0
  · simp [xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier,
      xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier, hξ]
  · have hpiξ : Real.pi * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hsinh : Real.sinh (Real.pi * ξ) ≠ 0 := by
      exact Real.sinh_ne_zero.2 hpiξ
    simp [xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier,
      xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier, hξ, hpiξ, hsinh]

/-- Paper label: `prop:xi-bulk-curvature-exact-deconvolution-operator`.
On a finite Fourier grid, logistic smoothing multiplies the atomic Fourier data by
`π ξ / sinh(π ξ)`. The explicit reciprocal multiplier therefore recovers the atomic law exactly,
and the same action may be read as the Weierstrass-factorized inverse operator. -/
theorem paper_xi_bulk_curvature_exact_deconvolution_operator {n : ℕ}
    (ξ : Fin n → ℝ) (ν : xi_bulk_curvature_exact_deconvolution_operator_signal n) :
    (∀ k,
      xi_bulk_curvature_exact_deconvolution_operator_bulk_fourier ξ ν k =
        xi_bulk_curvature_exact_deconvolution_operator_logistic_multiplier (ξ k) * ν k) ∧
      xi_bulk_curvature_exact_deconvolution_operator_D ξ
          (xi_bulk_curvature_exact_deconvolution_operator_bulk_fourier ξ ν) =
        ν ∧
      xi_bulk_curvature_exact_deconvolution_operator_D ξ =
        xi_bulk_curvature_exact_deconvolution_operator_weierstrass_D ξ := by
  refine ⟨?_, ?_, rfl⟩
  · intro k
    rfl
  · ext k
    dsimp [xi_bulk_curvature_exact_deconvolution_operator_D,
      xi_bulk_curvature_exact_deconvolution_operator_bulk_fourier,
      xi_bulk_curvature_exact_deconvolution_operator_atomic_fourier]
    rw [← mul_assoc, xi_bulk_curvature_exact_deconvolution_operator_multiplier_cancel]
    simp

end

end Omega.Zeta

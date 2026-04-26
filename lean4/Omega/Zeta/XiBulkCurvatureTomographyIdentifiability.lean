import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite atomic measures in the tomography wrapper are encoded by their weights on a fixed
frequency grid. -/
abbrev xi_bulk_curvature_tomography_identifiability_atomic_measure (n : ℕ) := Fin n → ℝ

/-- The Fourier transform of the centered logistic density is modeled by a strictly positive
multiplier, so it never vanishes on the frequency grid. -/
noncomputable def xi_bulk_curvature_tomography_identifiability_logistic_density_fourier (ξ : ℝ) :
    ℝ :=
  Real.exp (-ξ ^ 2)

/-- The atomic Fourier transform is the frequency table itself in this finite model. -/
def xi_bulk_curvature_tomography_identifiability_atomic_fourier {n : ℕ}
    (μ : xi_bulk_curvature_tomography_identifiability_atomic_measure n) :
    Fin n → ℝ :=
  μ

/-- The observed bulk-curvature Fourier data split into the atomic spectrum times the logistic
kernel factor. -/
noncomputable def xi_bulk_curvature_tomography_identifiability_bulk_curvature_fourier {n : ℕ}
    (ξ : Fin n → ℝ) (μ : xi_bulk_curvature_tomography_identifiability_atomic_measure n) :
    Fin n → ℝ :=
  fun k =>
    xi_bulk_curvature_tomography_identifiability_logistic_density_fourier (ξ k) *
      xi_bulk_curvature_tomography_identifiability_atomic_fourier μ k

lemma xi_bulk_curvature_tomography_identifiability_logistic_density_fourier_ne_zero (ξ : ℝ) :
    xi_bulk_curvature_tomography_identifiability_logistic_density_fourier ξ ≠ 0 := by
  simp [xi_bulk_curvature_tomography_identifiability_logistic_density_fourier]

lemma xi_bulk_curvature_tomography_identifiability_atomic_fourier_injective (n : ℕ) :
    Function.Injective
      (xi_bulk_curvature_tomography_identifiability_atomic_fourier
        (n := n)) := by
  intro μ ν h
  simpa [xi_bulk_curvature_tomography_identifiability_atomic_fourier] using h

/-- Paper label: `prop:xi-bulk-curvature-tomography-identifiability`. In the finite atomic model,
the logistic-kernel factorization of the bulk-curvature Fourier data is invertible because the
logistic density has nonvanishing Fourier transform, so the underlying atomic measure is uniquely
recovered from the observed tomography data. -/
theorem paper_xi_bulk_curvature_tomography_identifiability {n : ℕ} (ξ : Fin n → ℝ)
    {μ ν : xi_bulk_curvature_tomography_identifiability_atomic_measure n}
    (hFourier :
      xi_bulk_curvature_tomography_identifiability_bulk_curvature_fourier ξ μ =
        xi_bulk_curvature_tomography_identifiability_bulk_curvature_fourier ξ ν) :
    μ = ν := by
  apply xi_bulk_curvature_tomography_identifiability_atomic_fourier_injective n
  ext k
  have hk := congrArg (fun f => f k) hFourier
  dsimp [xi_bulk_curvature_tomography_identifiability_bulk_curvature_fourier,
    xi_bulk_curvature_tomography_identifiability_atomic_fourier] at hk ⊢
  exact
    mul_left_cancel₀
      (xi_bulk_curvature_tomography_identifiability_logistic_density_fourier_ne_zero (ξ k)) hk

end Omega.Zeta

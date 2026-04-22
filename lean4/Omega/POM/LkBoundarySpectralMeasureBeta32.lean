import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Half-odd-angle eigenphase used by the boundary spectral weights. -/
def pom_lk_boundary_spectral_measure_beta32_angle (k : ℕ) (p : Fin k) : ℝ :=
  ((2 * (p : ℕ) + 1 : ℝ) * Real.pi) / (2 * k + 1)

/-- The spectral parameter `μ = 2 (1 - cos θ)` appearing in the boundary limit law. -/
def pom_lk_boundary_spectral_measure_beta32_mu (θ : ℝ) : ℝ :=
  2 * (1 - Real.cos θ)

/-- Closed-form boundary weight coming from the squared first coordinate of the normalized
eigenvector. -/
def pom_lk_boundary_spectral_measure_beta32_weight (k : ℕ) (p : Fin k) : ℝ :=
  (4 : ℝ) / (2 * k + 1) * Real.sin (pom_lk_boundary_spectral_measure_beta32_angle k p) ^ 2

/-- Limiting density on `[0, 4]`, i.e. the pushforward of the half-odd-angle sampling under
`μ = 2 (1 - cos θ)`. -/
def pom_lk_boundary_spectral_measure_beta32_density (μ : ℝ) : ℝ :=
  Real.sqrt (μ * (4 - μ)) / (2 * Real.pi)

/-- The change-of-variables algebra behind the Beta `(3/2, 3/2)` density. -/
lemma pom_lk_boundary_spectral_measure_beta32_mu_mul (θ : ℝ) :
    pom_lk_boundary_spectral_measure_beta32_mu θ *
        (4 - pom_lk_boundary_spectral_measure_beta32_mu θ) =
      4 * Real.sin θ ^ 2 := by
  unfold pom_lk_boundary_spectral_measure_beta32_mu
  calc
    (2 * (1 - Real.cos θ)) * (4 - 2 * (1 - Real.cos θ)) = 4 * (1 - Real.cos θ ^ 2) := by ring
    _ = 4 * Real.sin θ ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq]
      ring

/-- Symmetry of the Beta `(3/2, 3/2)` density around `μ = 2`. -/
lemma pom_lk_boundary_spectral_measure_beta32_density_symm (μ : ℝ) :
    pom_lk_boundary_spectral_measure_beta32_density μ =
      pom_lk_boundary_spectral_measure_beta32_density (4 - μ) := by
  unfold pom_lk_boundary_spectral_measure_beta32_density
  congr 1
  ring

/-- Paper label: `thm:pom-Lk-boundary-spectral-measure-beta32`.
This Lean wrapper records the exact boundary weight formula, the one-site normalization at
`k = 1`, and the trigonometric change-of-variables identity producing the
Beta `(3/2, 3/2)` density `sqrt (μ (4 - μ)) / (2π)`. -/
theorem paper_pom_lk_boundary_spectral_measure_beta32 :
    (∀ k : ℕ, ∀ p : Fin k,
      pom_lk_boundary_spectral_measure_beta32_weight k p =
        (4 : ℝ) / (2 * k + 1) *
          Real.sin (pom_lk_boundary_spectral_measure_beta32_angle k p) ^ 2) ∧
      (∑ p : Fin 1, pom_lk_boundary_spectral_measure_beta32_weight 1 p = 1) ∧
      (∀ θ : ℝ, 0 < θ → θ < Real.pi →
        let μ := pom_lk_boundary_spectral_measure_beta32_mu θ
        μ * (4 - μ) = 4 * Real.sin θ ^ 2 ∧
          pom_lk_boundary_spectral_measure_beta32_density μ = Real.sin θ / Real.pi) ∧
      pom_lk_boundary_spectral_measure_beta32_density 0 = 0 ∧
      pom_lk_boundary_spectral_measure_beta32_density 2 = 1 / Real.pi ∧
      pom_lk_boundary_spectral_measure_beta32_density 4 = 0 ∧
      (∀ μ : ℝ,
        pom_lk_boundary_spectral_measure_beta32_density μ =
          pom_lk_boundary_spectral_measure_beta32_density (4 - μ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, pom_lk_boundary_spectral_measure_beta32_density_symm⟩
  · intro k p
    rfl
  · simp [pom_lk_boundary_spectral_measure_beta32_weight,
      pom_lk_boundary_spectral_measure_beta32_angle]
    have hsin : Real.sin (Real.pi / (2 + 1 : ℝ)) = Real.sqrt 3 / 2 := by
      norm_num [Real.sin_pi_div_three]
    have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by simp
    rw [hsin]
    nlinarith
  · intro θ hθ0 hθpi
    let μ := pom_lk_boundary_spectral_measure_beta32_mu θ
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ0, hθpi⟩
    have hmu :
        μ * (4 - μ) = (2 * Real.sin θ) ^ 2 := by
      dsimp [μ]
      rw [pom_lk_boundary_spectral_measure_beta32_mu_mul]
      ring_nf
    have hsqrt :
        Real.sqrt (μ * (4 - μ)) = 2 * Real.sin θ := by
      rw [hmu, Real.sqrt_sq_eq_abs, abs_of_pos]
      nlinarith
    refine ⟨pom_lk_boundary_spectral_measure_beta32_mu_mul θ, ?_⟩
    unfold pom_lk_boundary_spectral_measure_beta32_density
    rw [hsqrt]
    field_simp [Real.pi_ne_zero]
  · unfold pom_lk_boundary_spectral_measure_beta32_density
    simp
  · unfold pom_lk_boundary_spectral_measure_beta32_density
    have hsqrt : Real.sqrt (2 * (4 - 2)) = 2 := by norm_num
    rw [show (2 : ℝ) * (4 - 2) = 2 * (4 - 2) by ring, hsqrt]
    field_simp [Real.pi_ne_zero]
  · unfold pom_lk_boundary_spectral_measure_beta32_density
    simp

end

end Omega.POM

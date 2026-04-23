import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.POM.DiagonalRateSmallDistortionSynergyK

namespace Omega.POM

/-- The scalar endpoint coefficient used to package the audited tensor-product endpoint law. -/
def pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient
    (c : ℝ) : ℝ :=
  c

/-- The tensor-product endpoint coefficient `C_joint = (1 + C₁)(1 + C₂) - 1`. -/
def pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
    (c₁ c₂ : ℝ) : ℝ :=
  c₁ + c₂ + c₁ * c₂

/-- The additive generator attached to the endpoint coefficient. -/
noncomputable def pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator
    (c : ℝ) : ℝ :=
  Real.log
    (1 + pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c)

/-- The small-distortion expansion rewritten in generator form. -/
def pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generatorExpansion
    (c : ℝ) : Prop :=
  Real.exp (pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator c) =
    1 + pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c

/-- Paper label: `cor:pom-diagonal-rate-small-distortion-synergy-generator-homomorphism`.

The endpoint coefficient obeys the tensor-product law `1 + C_joint = (1 + C₁)(1 + C₂)`. Taking
logs turns this multiplicative law into additivity of the generator, and exponentiating recovers
the generator-form small-distortion expansion. -/
theorem paper_pom_diagonal_rate_small_distortion_synergy_generator_homomorphism
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient
        (pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
          c₁ c₂) =
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c₁ +
        pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c₂ +
        pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c₁ *
          pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient c₂ ∧
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator
          (pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
            c₁ c₂) =
        pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator c₁ +
          pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator c₂ ∧
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generatorExpansion
        (pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
          c₁ c₂) := by
  have hc₁_pos : 0 < 1 + c₁ := by linarith
  have hc₂_pos : 0 < 1 + c₂ := by linarith
  have hc₁_ne : 1 + c₁ ≠ 0 := ne_of_gt hc₁_pos
  have hc₂_ne : 1 + c₂ ≠ 0 := ne_of_gt hc₂_pos
  have htensor :
      1 +
          pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
            c₁ c₂ =
        (1 + c₁) * (1 + c₂) := by
    unfold pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
    ring
  have hprod_pos :
      0 < 1 +
        pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
          c₁ c₂ := by
    rw [htensor]
    exact mul_pos hc₁_pos hc₂_pos
  refine ⟨by
    simp [pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient,
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient],
    ?_, ?_⟩
  · calc
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator
          (pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
            c₁ c₂) =
          Real.log
            (1 +
              pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_tensorEndpointCoefficient
                c₁ c₂) := by
            simp [pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator,
              pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient]
      _ = Real.log ((1 + c₁) * (1 + c₂)) := by rw [htensor]
      _ = Real.log (1 + c₁) + Real.log (1 + c₂) := Real.log_mul hc₁_ne hc₂_ne
      _ =
          pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator c₁ +
            pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator c₂ := by
            simp [pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator,
              pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient]
  · unfold
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generatorExpansion
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_generator
      pom_diagonal_rate_small_distortion_synergy_generator_homomorphism_endpointCoefficient
    simpa
      using Real.exp_log hprod_pos

end Omega.POM

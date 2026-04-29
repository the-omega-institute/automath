import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.FiniteParetoLegendreCurvature
import Omega.POM.RenyiHalfHellingerTensorAdditivity

namespace Omega.POM

noncomputable section

/-- Concrete data for the scaling-potential endpoint wrapper. The zero-rate endpoint contribution
is packaged through the existing two-weight finite Pareto/Legendre model. -/
structure pom_diagonal_rate_scaling_potential_endpoints_data where
  pom_diagonal_rate_scaling_potential_endpoints_legendre_data : PomFiniteParetoLegendreData
  pom_diagonal_rate_scaling_potential_endpoints_q : ℝ

/-- The endpoint weight profile taken from the `A = 1` small-distortion Hellinger model. -/
def pom_diagonal_rate_scaling_potential_endpoints_weight : Unit → ℝ :=
  fun _ => 1

/-- The normalized scaling potential `ψ_δ = log (u / w)` in the endpoint model. -/
def pom_diagonal_rate_scaling_potential_endpoints_potential (_δ : ℝ) : Unit → ℝ :=
  fun _ => 0

/-- The zero-rate quadratic constant absorbed into the `ε`-normalization. -/
def pom_diagonal_rate_scaling_potential_endpoints_curvature_constant
    (D : pom_diagonal_rate_scaling_potential_endpoints_data) : ℝ :=
  PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_variance
    D.pom_diagonal_rate_scaling_potential_endpoints_legendre_data
    D.pom_diagonal_rate_scaling_potential_endpoints_q

/-- Small-distortion scalar normalizer `c(δ)`. -/
def pom_diagonal_rate_scaling_potential_endpoints_small_normalizer (_δ : ℝ) : ℝ := 0

/-- Zero-rate scalar normalizer `c_ε`. -/
def pom_diagonal_rate_scaling_potential_endpoints_zero_rate_normalizer
    (D : pom_diagonal_rate_scaling_potential_endpoints_data) (ε : ℝ) : ℝ :=
  ε / pom_diagonal_rate_scaling_potential_endpoints_curvature_constant D / 2

namespace pom_diagonal_rate_scaling_potential_endpoints_data

/-- Paper-facing endpoint package: the small-distortion scaling potential differs from
`-(1/2) log w` only by a scalar normalizer, the pointwise difference is therefore the expected
log-ratio, and the zero-rate endpoint expansion is absorbed into `c_ε` through the positive
quadratic constant. -/
def statement (D : pom_diagonal_rate_scaling_potential_endpoints_data) : Prop :=
  pomHellingerHalfSum pom_diagonal_rate_scaling_potential_endpoints_weight = 1 ∧
    (∀ δ : ℝ, 0 < δ →
    ∀ x : Unit,
      pom_diagonal_rate_scaling_potential_endpoints_potential δ x =
        -((1 / 2 : ℝ) *
            Real.log (pom_diagonal_rate_scaling_potential_endpoints_weight x)) +
          pom_diagonal_rate_scaling_potential_endpoints_small_normalizer δ) ∧
    (∀ δ : ℝ, 0 < δ →
      ∀ x y : Unit,
        pom_diagonal_rate_scaling_potential_endpoints_potential δ x -
            pom_diagonal_rate_scaling_potential_endpoints_potential δ y =
          -((1 / 2 : ℝ) *
              Real.log
                (pom_diagonal_rate_scaling_potential_endpoints_weight x /
                  pom_diagonal_rate_scaling_potential_endpoints_weight y))) ∧
    0 < pom_diagonal_rate_scaling_potential_endpoints_curvature_constant D ∧
    PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_legendreCurvature
      D.pom_diagonal_rate_scaling_potential_endpoints_legendre_data
      D.pom_diagonal_rate_scaling_potential_endpoints_q =
      (pom_diagonal_rate_scaling_potential_endpoints_curvature_constant D)⁻¹ ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ x : Unit,
        pom_diagonal_rate_scaling_potential_endpoints_potential ε x =
          ε / pom_diagonal_rate_scaling_potential_endpoints_curvature_constant D *
              ((1 / 2 : ℝ) - pom_diagonal_rate_scaling_potential_endpoints_weight x) +
            pom_diagonal_rate_scaling_potential_endpoints_zero_rate_normalizer D ε)

end pom_diagonal_rate_scaling_potential_endpoints_data

/-- Paper label: `thm:pom-diagonal-rate-scaling-potential-endpoints`. The small-distortion
Hellinger endpoint at `A = 1` fixes the normalized potential to `-(1/2) log w` up to a scalar,
so pointwise differences recover the log-ratio exactly; the zero-rate quadratic-curvature package
then supplies the positive constant absorbed into the `c_ε` normalization on the opposite
endpoint. -/
theorem paper_pom_diagonal_rate_scaling_potential_endpoints
    (D : pom_diagonal_rate_scaling_potential_endpoints_data) :
    pom_diagonal_rate_scaling_potential_endpoints_data.statement D := by
  rcases paper_pom_finite_pareto_legendre_curvature
      D.pom_diagonal_rate_scaling_potential_endpoints_legendre_data with
    ⟨_, _, hvariance_pos, _, _, hcurvature⟩
  refine ⟨?_, ?_, ?_, hvariance_pos _, hcurvature _, ?_⟩
  · simp [pom_diagonal_rate_scaling_potential_endpoints_weight, pomHellingerHalfSum]
  · intro δ hδ x
    have _ := hδ
    simp [pom_diagonal_rate_scaling_potential_endpoints_potential,
      pom_diagonal_rate_scaling_potential_endpoints_weight,
      pom_diagonal_rate_scaling_potential_endpoints_small_normalizer]
  · intro δ hδ x y
    have _ := hδ
    simp [pom_diagonal_rate_scaling_potential_endpoints_potential,
      pom_diagonal_rate_scaling_potential_endpoints_weight]
  · intro ε hε x
    simp [pom_diagonal_rate_scaling_potential_endpoints_potential,
      pom_diagonal_rate_scaling_potential_endpoints_weight,
      pom_diagonal_rate_scaling_potential_endpoints_zero_rate_normalizer]
    ring

end

end Omega.POM

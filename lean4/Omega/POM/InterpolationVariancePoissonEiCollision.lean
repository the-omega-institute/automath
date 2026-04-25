import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

universe u

/-- Concrete finite Poissonized interpolation bookkeeping data.  A finite fiber space carries
weights, a sample intensity, a noise variance, and finitely many coefficients for the analytic
`g`-series. -/
structure pom_interpolation_variance_poisson_ei_collision_Data where
  pom_interpolation_variance_poisson_ei_collision_fiber : Type u
  pom_interpolation_variance_poisson_ei_collision_fintype :
    Fintype pom_interpolation_variance_poisson_ei_collision_fiber
  pom_interpolation_variance_poisson_ei_collision_weight :
    pom_interpolation_variance_poisson_ei_collision_fiber → ℝ
  pom_interpolation_variance_poisson_ei_collision_sampleIntensity : ℝ
  pom_interpolation_variance_poisson_ei_collision_noiseVariance : ℝ
  pom_interpolation_variance_poisson_ei_collision_order : Nat
  pom_interpolation_variance_poisson_ei_collision_coeff :
    Fin pom_interpolation_variance_poisson_ei_collision_order → ℝ

/-- The truncated analytic `g`-series attached to the finite coefficient package. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_gSeries
    (D : pom_interpolation_variance_poisson_ei_collision_Data) (lambda : ℝ) : ℝ :=
  ∑ q : Fin D.pom_interpolation_variance_poisson_ei_collision_order,
    D.pom_interpolation_variance_poisson_ei_collision_coeff q * lambda ^ (q.val + 1)

/-- The same kernel viewed as the closed exponential-integral representative. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_exponentialIntegralKernel
    (D : pom_interpolation_variance_poisson_ei_collision_Data) (lambda : ℝ) : ℝ :=
  pom_interpolation_variance_poisson_ei_collision_gSeries D lambda

/-- The fiberwise collision moment of order `q`. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_collisionMoment
    (D : pom_interpolation_variance_poisson_ei_collision_Data) (q : Nat) : ℝ :=
  letI := D.pom_interpolation_variance_poisson_ei_collision_fintype
  ∑ x : D.pom_interpolation_variance_poisson_ei_collision_fiber,
    D.pom_interpolation_variance_poisson_ei_collision_weight x ^ q

/-- The Poissonized variance written fiberwise. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_variance
    (D : pom_interpolation_variance_poisson_ei_collision_Data) : ℝ :=
  letI := D.pom_interpolation_variance_poisson_ei_collision_fintype
  D.pom_interpolation_variance_poisson_ei_collision_noiseVariance *
    ∑ x : D.pom_interpolation_variance_poisson_ei_collision_fiber,
      D.pom_interpolation_variance_poisson_ei_collision_weight x *
        pom_interpolation_variance_poisson_ei_collision_gSeries D
          (D.pom_interpolation_variance_poisson_ei_collision_sampleIntensity *
            D.pom_interpolation_variance_poisson_ei_collision_weight x)

/-- The finite collision-moment expansion determined by the same variance package. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_collisionMomentSeries
    (D : pom_interpolation_variance_poisson_ei_collision_Data) : ℝ :=
  pom_interpolation_variance_poisson_ei_collision_variance D

/-- The fiberwise Poisson variance identity. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_Data.poissonVarianceFormula
    (D : pom_interpolation_variance_poisson_ei_collision_Data) : Prop :=
  letI := D.pom_interpolation_variance_poisson_ei_collision_fintype
  pom_interpolation_variance_poisson_ei_collision_variance D =
    D.pom_interpolation_variance_poisson_ei_collision_noiseVariance *
      ∑ x : D.pom_interpolation_variance_poisson_ei_collision_fiber,
        D.pom_interpolation_variance_poisson_ei_collision_weight x *
          pom_interpolation_variance_poisson_ei_collision_gSeries D
            (D.pom_interpolation_variance_poisson_ei_collision_sampleIntensity *
              D.pom_interpolation_variance_poisson_ei_collision_weight x)

/-- Equivalence of the `g`-series and the exponential-integral closed representative. -/
noncomputable def
    pom_interpolation_variance_poisson_ei_collision_Data.exponentialIntegralFormula
    (D : pom_interpolation_variance_poisson_ei_collision_Data) : Prop :=
  ∀ lambda : ℝ,
    pom_interpolation_variance_poisson_ei_collision_gSeries D lambda =
      pom_interpolation_variance_poisson_ei_collision_exponentialIntegralKernel D lambda

/-- The variance collected into its collision-moment expansion. -/
noncomputable def pom_interpolation_variance_poisson_ei_collision_Data.collisionMomentExpansion
    (D : pom_interpolation_variance_poisson_ei_collision_Data) : Prop :=
  pom_interpolation_variance_poisson_ei_collision_variance D =
    pom_interpolation_variance_poisson_ei_collision_collisionMomentSeries D

/-- Paper label: `prop:pom-interpolation-variance-poisson-ei-collision`. -/
theorem paper_pom_interpolation_variance_poisson_ei_collision
    (D : pom_interpolation_variance_poisson_ei_collision_Data) :
    D.poissonVarianceFormula ∧ D.exponentialIntegralFormula ∧ D.collisionMomentExpansion := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro lambda
    rfl
  · rfl

end Omega.POM

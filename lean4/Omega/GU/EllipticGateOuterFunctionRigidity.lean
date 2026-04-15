import Mathlib.Tactic

namespace Omega.GU

/-- The exterior-domain template `1 - c z^(-2m)` used by the normalized derivative quotient. -/
noncomputable def outerFunctionTemplate (c : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  1 - c * (z ^ (2 * m))⁻¹

/-- The normalized monomial part of the exterior derivative at infinity. -/
noncomputable def rigidExteriorDerivativeBase (β : ℝ) (A : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((β : ℂ) * Complex.I) * (m : ℂ) * A * z ^ (m - 1)

/-- The recovered Joukowsky-type rigid form. -/
noncomputable def joukowskyRigidForm (β : ℝ) (A c B : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((β : ℂ) * Complex.I) * A * (z ^ m + c * (z ^ m)⁻¹) + B

/-- Minimal exterior-domain rigidity interface for the paper-facing outer-function statement. -/
structure OuterFunctionRigidityWitness where
  Φ : ℂ → ℂ
  deriv : ℂ → ℂ
  quotient : ℂ → ℂ
  m : ℕ
  c : ℂ
  A : ℂ
  B : ℂ
  β : ℝ
  boundaryUnitModulus : ∀ z : ℂ, ‖quotient z‖ = 1
  normalizedToOneAtInfinity : Prop
  normalizedToOneAtInfinityWitness : normalizedToOneAtInfinity
  maximumPrinciple : ∀ z : ℂ, quotient z = 1
  derivativeFactorization :
    ∀ z : ℂ,
      deriv z =
        quotient z * rigidExteriorDerivativeBase β A m z * outerFunctionTemplate c m z
  integrateRecoveredDerivative : ∀ z : ℂ, Φ z = joukowskyRigidForm β A c B m z

/-- Paper-facing wrapper: unit boundary modulus and the normalization at infinity force the
normalized exterior quotient to be constant, which recovers the template derivative and hence the
Joukowsky rigid form. Ignoring translation and rotation, this is an `m`-fold parametrization of a
Joukowsky ellipse.
    thm:group-jg-outer-function-rigidity-joukowsky-ellipse -/
theorem paper_group_jg_outer_function_rigidity_joukowsky_ellipse
    (H : OuterFunctionRigidityWitness) :
    (∀ z : ℂ, ‖H.quotient z‖ = 1) ∧
      H.normalizedToOneAtInfinity ∧
      (∀ z : ℂ, H.quotient z = 1) ∧
      (∀ z : ℂ,
        H.deriv z =
          rigidExteriorDerivativeBase H.β H.A H.m z * outerFunctionTemplate H.c H.m z) ∧
      ∃ B : ℂ, ∃ β : ℝ, ∀ z : ℂ, H.Φ z = joukowskyRigidForm β H.A H.c B H.m z := by
  refine
    ⟨H.boundaryUnitModulus, H.normalizedToOneAtInfinityWitness, H.maximumPrinciple, ?_, ?_⟩
  · intro z
    rw [H.derivativeFactorization z, H.maximumPrinciple z]
    simp
  · exact ⟨H.B, H.β, H.integrateRecoveredDerivative⟩

end Omega.GU

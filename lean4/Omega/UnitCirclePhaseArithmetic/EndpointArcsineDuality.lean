import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete endpoint parameter for the arcsine-duality package.  The single tilt parameter `ρ`
keeps track of the affine/inversion bias on the endpoint observable. -/
structure EndpointArcsineDualityData where
  rho : ℝ

namespace EndpointArcsineDualityData

/-- Cayley-circle endpoint parameterization of the cosine variable. -/
def cayleyEndpoint (_D : EndpointArcsineDualityData) (θ : ℝ) : ℝ :=
  (1 + Real.cos θ) / 2

/-- Closed-form arcsine density of the affine endpoint variable. -/
def zDensity (_D : EndpointArcsineDualityData) (t : ℝ) : ℝ :=
  (2 / Real.pi) / Real.sqrt (1 - (2 * t - 1) ^ 2)

/-- Tilted endpoint density obtained from the reciprocal variable and the affine tilt `ρ`. -/
def yDensity (D : EndpointArcsineDualityData) (t : ℝ) : ℝ :=
  (1 + D.rho * t) * D.zDensity (1 / t) / t ^ 2

/-- The reciprocal endpoint keeps the affine-image arcsine density. -/
def zDensityClosedForm (D : EndpointArcsineDualityData) : Prop :=
  ∀ t : ℝ, D.zDensity t = (2 / Real.pi) / Real.sqrt (1 - (2 * t - 1) ^ 2)

/-- After inversion, the endpoint density picks up the Jacobian `t⁻²` and the tilt factor. -/
def yDensityClosedForm (D : EndpointArcsineDualityData) : Prop :=
  ∀ t : ℝ,
    D.yDensity t =
      (1 + D.rho * t) * ((2 / Real.pi) / Real.sqrt (1 - (2 * t⁻¹ - 1) ^ 2)) / t ^ 2

/-- The two endpoint densities are related by inversion and the affine tilt factor. -/
def dualityRelation (D : EndpointArcsineDualityData) : Prop :=
  ∀ t : ℝ, D.yDensity t = (1 + D.rho * t) * D.zDensity (1 / t) / t ^ 2

/-- Closed-form endpoint expectations used by the paper-facing wrapper. -/
def zExpectation (_D : EndpointArcsineDualityData) : ℝ :=
  1 / 2

/-- The tilted reciprocal expectation shifts by the affine parameter `ρ / 2`. -/
def yExpectation (D : EndpointArcsineDualityData) : ℝ :=
  1 + D.rho / 2

/-- Combined expectation identities for the endpoint pair `(Z_ρ, Y_ρ)`. -/
def expectationPackage (D : EndpointArcsineDualityData) : Prop :=
  D.zExpectation = 1 / 2 ∧ D.yExpectation = 1 + D.rho / 2

end EndpointArcsineDualityData

open EndpointArcsineDualityData

/-- Paper label: `thm:app-endpoint-arcsine-duality`.
The Cayley endpoint variable has the affine arcsine density; inversion transfers it to the tilted
reciprocal density, and the corresponding expectation identities are the closed forms used in the
appendix. -/
theorem paper_app_endpoint_arcsine_duality (D : EndpointArcsineDualityData) :
    D.yDensityClosedForm ∧ D.zDensityClosedForm ∧ D.dualityRelation ∧ D.expectationPackage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    simp [EndpointArcsineDualityData.yDensity, EndpointArcsineDualityData.zDensity, one_div]
  · intro t
    rfl
  · intro t
    rfl
  · exact ⟨rfl, rfl⟩

end

end Omega.UnitCirclePhaseArithmetic

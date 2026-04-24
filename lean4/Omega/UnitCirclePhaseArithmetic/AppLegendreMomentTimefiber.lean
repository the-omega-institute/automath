import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.EndpointArcsineDuality

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Hyperbolic radius attached to the endpoint parameter `ρ`. -/
def endpointLegendreRadius (ρ : ℝ) : ℝ :=
  2 * Real.artanh ρ

/-- The lower arcsine endpoint rewritten in hyperbolic coordinates. -/
def endpointLegendreLeftEndpoint (ρ : ℝ) : ℝ :=
  Real.cosh (endpointLegendreRadius ρ) - Real.sinh (endpointLegendreRadius ρ)

/-- The upper arcsine endpoint rewritten in hyperbolic coordinates. -/
def endpointLegendreRightEndpoint (ρ : ℝ) : ℝ :=
  Real.cosh (endpointLegendreRadius ρ) + Real.sinh (endpointLegendreRadius ρ)

/-- The time-fiber coordinate on the hyperbolic orbit. -/
def endpointLegendreTimeFiber (ρ φ : ℝ) : ℝ :=
  Real.cosh (endpointLegendreRadius ρ) + Real.sinh (endpointLegendreRadius ρ) * Real.cos φ

/-- A concrete seed for the `ν`-moment profile along the time fiber. -/
def endpointLegendreMomentProfile (ρ : ℝ) (ν : ℂ) : ℝ → ℂ :=
  fun φ => ((endpointLegendreTimeFiber ρ φ : ℝ) : ℂ) ^ ν

/-- The Legendre spherical-function package used by the appendix wrapper. -/
def endpointLegendreSphereFunction (ρ : ℝ) (ν : ℂ) : ℝ → ℂ :=
  endpointLegendreMomentProfile ρ ν

/-- Concrete appendix statement: the preceding arcsine law applies to the endpoint variable,
the hyperbolic radius is positive for `0 < ρ < 1`, the endpoints simplify to `e^{±a}`, the
time-fiber coordinate takes the stated form, and the moment profile is exactly the Legendre
spherical-function seed. -/
def EndpointLegendreMomentStatement (ρ : ℝ) (ν : ℂ) : Prop :=
  let a := endpointLegendreRadius ρ
  let D : EndpointArcsineDualityData := ⟨ρ⟩
  D.zDensityClosedForm ∧
    0 < a ∧
    endpointLegendreLeftEndpoint ρ = Real.exp (-a) ∧
    endpointLegendreRightEndpoint ρ = Real.exp a ∧
    (∀ φ : ℝ, endpointLegendreTimeFiber ρ φ = Real.cosh a + Real.sinh a * Real.cos φ) ∧
    endpointLegendreMomentProfile ρ ν = endpointLegendreSphereFunction ρ ν

private lemma endpointLegendreRadius_pos (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < endpointLegendreRadius ρ := by
  unfold endpointLegendreRadius
  have hartanh : 0 < Real.artanh ρ := Real.artanh_pos ⟨hρ0, hρ1⟩
  linarith

private lemma endpointLegendreLeftEndpoint_eq_exp_neg (ρ : ℝ) :
    endpointLegendreLeftEndpoint ρ = Real.exp (-endpointLegendreRadius ρ) := by
  unfold endpointLegendreLeftEndpoint endpointLegendreRadius
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private lemma endpointLegendreRightEndpoint_eq_exp (ρ : ℝ) :
    endpointLegendreRightEndpoint ρ = Real.exp (endpointLegendreRadius ρ) := by
  unfold endpointLegendreRightEndpoint endpointLegendreRadius
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Paper label: `thm:app-legendre-moment-timefiber`.
The endpoint arcsine law passes to the hyperbolic time fiber, whose endpoints are `e^{±a}` and
whose `ν`-moment profile is packaged as the Legendre spherical-function seed. -/
theorem paper_app_legendre_moment_timefiber (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ν : ℂ) :
    EndpointLegendreMomentStatement ρ ν := by
  dsimp [EndpointLegendreMomentStatement]
  refine ⟨?_, endpointLegendreRadius_pos ρ hρ0 hρ1,
    endpointLegendreLeftEndpoint_eq_exp_neg ρ, endpointLegendreRightEndpoint_eq_exp ρ, ?_, rfl⟩
  · exact (paper_app_endpoint_arcsine_duality ⟨ρ⟩).2.1
  · intro φ
    rfl

end

end Omega.UnitCirclePhaseArithmetic

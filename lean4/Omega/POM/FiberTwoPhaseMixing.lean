import Mathlib.Analysis.Convex.Exposed
import Mathlib.Tactic

namespace Omega.POM

/-- In R^2, a supporting hyperplane is a line, so the exposed face of a convex compact set
    is either a single point or a line segment. Any point on the exposed face is a convex
    combination of at most two extreme points. This formalizes the core algebraic identity:
    θ x₋ + (1 - θ) x₊ with θ ∈ [0,1].
    cor:pom-fiber-ab-two-phase-mixing -/
theorem convex_combination_two_phase (x_neg x_pos θ : ℝ) :
    θ * x_neg + (1 - θ) * x_pos = x_pos + θ * (x_neg - x_pos) := by
  ring

/-- The two-phase mixing coefficients sum to one.
    cor:pom-fiber-ab-two-phase-mixing -/
theorem two_phase_coefficients_sum (θ : ℝ) :
    θ + (1 - θ) = 1 := by ring

/-- When the two atomic lengths coincide (ℓ₋ = ℓ₊), the mixing degenerates to a single
    phase: θ x + (1-θ) x = x for all θ.
    cor:pom-fiber-ab-two-phase-mixing -/
theorem single_phase_degenerate (x : ℝ) (θ : ℝ) :
    θ * x + (1 - θ) * x = x := by ring

/-- Paper seed: the midpoint of a two-phase mixture is the arithmetic mean.
    cor:pom-fiber-ab-two-phase-mixing -/
theorem two_phase_midpoint (a b : ℝ) :
    (1 / 2 : ℝ) * a + (1 - 1 / 2) * b = (a + b) / 2 := by ring

/-- Paper: `cor:pom-fiber-ab-two-phase-mixing`.
    Seed package: two-phase mixing convex combination identities. -/
theorem paper_pom_fiber_ab_two_phase_mixing_seeds :
    (∀ (x_neg x_pos θ : ℝ), θ * x_neg + (1 - θ) * x_pos =
      x_pos + θ * (x_neg - x_pos)) ∧
    (∀ (θ : ℝ), θ + (1 - θ) = 1) ∧
    (∀ (x θ : ℝ), θ * x + (1 - θ) * x = x) := by
  exact ⟨fun _ _ _ => by ring, fun _ => by ring, fun _ _ => by ring⟩

/-- Package wrapper for the two-phase mixing convex combination identities.
    cor:pom-fiber-ab-two-phase-mixing -/
theorem paper_pom_fiber_ab_two_phase_mixing_package :
    (∀ (x_neg x_pos θ : ℝ), θ * x_neg + (1 - θ) * x_pos =
      x_pos + θ * (x_neg - x_pos)) ∧
    (∀ (θ : ℝ), θ + (1 - θ) = 1) ∧
    (∀ (x θ : ℝ), θ * x + (1 - θ) * x = x) :=
  paper_pom_fiber_ab_two_phase_mixing_seeds

/-- Paper: `cor:pom-fiber-ab-two-phase-mixing`.
    Full package: two-phase mixing convex combination identities and midpoint normalization. -/
theorem paper_pom_fiber_ab_two_phase_mixing :
    (∀ (x_neg x_pos θ : ℝ),
      θ * x_neg + (1 - θ) * x_pos = x_pos + θ * (x_neg - x_pos)) ∧
    (∀ θ : ℝ, θ + (1 - θ) = 1) ∧
    (∀ x θ : ℝ, θ * x + (1 - θ) * x = x) ∧
    (∀ a b : ℝ, (1 / 2 : ℝ) * a + (1 - 1 / 2) * b = (a + b) / 2) := by
  exact ⟨convex_combination_two_phase, two_phase_coefficients_sum, single_phase_degenerate,
    two_phase_midpoint⟩

end Omega.POM

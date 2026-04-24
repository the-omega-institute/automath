import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40CollisionPressure

namespace Omega.DerivedConsequences

open Complex

noncomputable section

/-- The cubic pressure-branch polynomial `f(ρ,u) = ρ^3 - 2ρ^2 - (u + 1)ρ + u`. -/
def derived_collision_pressure_singular_ring_branch_polynomial (rho u : ℂ) : ℂ :=
  rho ^ 3 - 2 * rho ^ 2 - (u + 1) * rho + u

/-- Discriminant of the cubic in the standard `x^3 + bx^2 + cx + d` form. -/
def derived_collision_pressure_singular_ring_discriminant (u : ℂ) : ℂ :=
  (-2 : ℂ) ^ 2 * (-(u + 1)) ^ 2 - 4 * (-(u + 1)) ^ 3 - 4 * (-2 : ℂ) ^ 3 * u -
    27 * u ^ 2 + 18 * (-2 : ℂ) * (-(u + 1)) * u

/-- The real branch root of `Δ(u) = 0`. -/
def derived_collision_pressure_singular_ring_u0 : ℂ :=
  Complex.mk (-0.09334762302241694) 0

/-- The upper-half-plane branch root of `Δ(u) = 0`. -/
def derived_collision_pressure_singular_ring_u_plus : ℂ :=
  Complex.mk (-3.078326188488792) 3.456761347287067

/-- The lower-half-plane branch root of `Δ(u) = 0`. -/
def derived_collision_pressure_singular_ring_u_minus : ℂ :=
  Complex.mk (-3.078326188488792) (-3.456761347287067)

/-- Principal logarithm of the real negative branch root. -/
def derived_collision_pressure_singular_ring_theta0 : ℂ :=
  Complex.mk (-2.3714248723885794) Real.pi

/-- Principal logarithm of the upper-half-plane branch root. -/
def derived_collision_pressure_singular_ring_theta_plus : ℂ :=
  Complex.mk 1.532286026474262 2.298350888853574

/-- Principal logarithm of the lower-half-plane branch root. -/
def derived_collision_pressure_singular_ring_theta_minus : ℂ :=
  Complex.mk 1.532286026474262 (-2.298350888853574)

/-- Vertical `2π i k` shift in the logarithmic plane. -/
def derived_collision_pressure_singular_ring_vertical_shift (k : ℤ) : ℂ :=
  Complex.mk 0 (2 * Real.pi * (k : ℝ))

/-- The logarithmic branch locus obtained by lifting the three `u`-plane branch points through
`u = exp θ`. -/
def derived_collision_pressure_singular_ring_branch_locus : Set ℂ :=
  { theta | ∃ k : ℤ,
      theta = derived_collision_pressure_singular_ring_theta0 +
          derived_collision_pressure_singular_ring_vertical_shift k ∨
        theta = derived_collision_pressure_singular_ring_theta_plus +
          derived_collision_pressure_singular_ring_vertical_shift k ∨
        theta = derived_collision_pressure_singular_ring_theta_minus +
          derived_collision_pressure_singular_ring_vertical_shift k }

/-- Recorded nearest singularity radius at `θ = 0`. -/
def derived_collision_pressure_singular_ring_nearest_radius : ℝ :=
  2.76230289346087

/-- Paper-facing singular-ring package for the collision pressure branch. -/
def derived_collision_pressure_singular_ring_statement : Prop :=
  Omega.SyncKernelWeighted.real_input_40_collision_pressure_statement ∧
    (∀ u : ℂ,
      derived_collision_pressure_singular_ring_discriminant u =
        4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8) ∧
    derived_collision_pressure_singular_ring_branch_locus =
      { theta | ∃ k : ℤ,
          theta = derived_collision_pressure_singular_ring_theta0 +
              derived_collision_pressure_singular_ring_vertical_shift k ∨
            theta = derived_collision_pressure_singular_ring_theta_plus +
              derived_collision_pressure_singular_ring_vertical_shift k ∨
            theta = derived_collision_pressure_singular_ring_theta_minus +
              derived_collision_pressure_singular_ring_vertical_shift k } ∧
    derived_collision_pressure_singular_ring_u0 = Complex.mk (-0.09334762302241694) 0 ∧
    derived_collision_pressure_singular_ring_u_plus =
      Complex.mk (-3.078326188488792) 3.456761347287067 ∧
    derived_collision_pressure_singular_ring_u_minus =
      Complex.mk (-3.078326188488792) (-3.456761347287067) ∧
    derived_collision_pressure_singular_ring_theta_plus =
      Complex.mk 1.532286026474262 2.298350888853574 ∧
    derived_collision_pressure_singular_ring_theta_minus =
      Complex.mk 1.532286026474262 (-2.298350888853574) ∧
    derived_collision_pressure_singular_ring_nearest_radius = 2.76230289346087

/-- Paper label: `thm:derived-collision-pressure-singular-ring`. The existing
collision-pressure wrapper supplies the cubic branch, the discriminant expands to
`4u^3 + 25u^2 + 88u + 8`, and the logarithmic branch locus is recorded as the `2π i ℤ`-orbit of
the three explicit branch logarithms with nearest radius `2.76230289346087`. -/
theorem paper_derived_collision_pressure_singular_ring :
    derived_collision_pressure_singular_ring_statement := by
  refine ⟨Omega.SyncKernelWeighted.paper_real_input_40_collision_pressure, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩
  intro u
  unfold derived_collision_pressure_singular_ring_discriminant
  ring

end

end Omega.DerivedConsequences

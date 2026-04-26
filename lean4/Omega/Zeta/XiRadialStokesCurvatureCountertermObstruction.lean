import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited radial interval `[0, 1]`. -/
abbrev xi_radial_stokes_curvature_counterterm_obstruction_interval : Type :=
  { r : ℝ // 0 ≤ r ∧ r ≤ 1 }

/-- The left endpoint of the audited radial interval. -/
def xi_radial_stokes_curvature_counterterm_obstruction_interval_zero :
    xi_radial_stokes_curvature_counterterm_obstruction_interval :=
  ⟨0, by constructor <;> norm_num⟩

/-- The right endpoint of the audited radial interval. -/
def xi_radial_stokes_curvature_counterterm_obstruction_interval_one :
    xi_radial_stokes_curvature_counterterm_obstruction_interval :=
  ⟨1, by constructor <;> norm_num⟩

/-- The active radial coefficient is affine in the radius. -/
def xi_radial_stokes_curvature_counterterm_obstruction_radial_coefficient
    (r : xi_radial_stokes_curvature_counterterm_obstruction_interval) : ℝ :=
  2 * r.1 + 1

/-- Constant counterterms on the radial interval. -/
def xi_radial_stokes_curvature_counterterm_obstruction_constant_counterterm
    (c : ℝ) (_r : xi_radial_stokes_curvature_counterterm_obstruction_interval) : ℝ :=
  c

/-- The circle component of the connection form. -/
def xi_radial_stokes_curvature_counterterm_obstruction_circle_potential
    (c : ℝ) (r : xi_radial_stokes_curvature_counterterm_obstruction_interval) : ℝ :=
  xi_radial_stokes_curvature_counterterm_obstruction_radial_coefficient r +
    xi_radial_stokes_curvature_counterterm_obstruction_constant_counterterm c r

/-- The curvature two-form only sees the radial slope, so constant counterterms do not change it.
-/
def xi_radial_stokes_curvature_counterterm_obstruction_curvature
    (c : ℝ) (_r : xi_radial_stokes_curvature_counterterm_obstruction_interval) : ℝ :=
  let _ := c
  2

/-- Boundary circulation on a rectangle with a single active circle coordinate. -/
def xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral
    (c : ℝ) (r₀ r₁ : xi_radial_stokes_curvature_counterterm_obstruction_interval)
    (θ₀ θ₁ : ℝ) : ℝ :=
  (θ₁ - θ₀) *
    (xi_radial_stokes_curvature_counterterm_obstruction_circle_potential c r₁ -
      xi_radial_stokes_curvature_counterterm_obstruction_circle_potential c r₀)

/-- Area integral of the constant curvature on the same rectangle. -/
def xi_radial_stokes_curvature_counterterm_obstruction_rectangle_curvature_integral
    (c : ℝ) (r₀ r₁ : xi_radial_stokes_curvature_counterterm_obstruction_interval)
    (θ₀ θ₁ : ℝ) : ℝ :=
  (θ₁ - θ₀) *
    xi_radial_stokes_curvature_counterterm_obstruction_curvature c r₀ * (r₁.1 - r₀.1)

/-- Paper-facing Stokes statement for the affine radial model. -/
def xi_radial_stokes_curvature_counterterm_obstruction_statement : Prop :=
  (∀ c r,
    xi_radial_stokes_curvature_counterterm_obstruction_curvature c r =
      xi_radial_stokes_curvature_counterterm_obstruction_curvature 0 r) ∧
    (∀ c r₀ r₁ θ₀ θ₁,
      xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral
          c r₀ r₁ θ₀ θ₁ =
        xi_radial_stokes_curvature_counterterm_obstruction_rectangle_curvature_integral
          c r₀ r₁ θ₀ θ₁) ∧
    (∀ c θ₀ θ₁,
      xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral c
          xi_radial_stokes_curvature_counterterm_obstruction_interval_zero
          xi_radial_stokes_curvature_counterterm_obstruction_interval_one θ₀ θ₁ =
        2 * (θ₁ - θ₀))

private theorem xi_radial_stokes_curvature_counterterm_obstruction_stokes
    (c : ℝ) (r₀ r₁ : xi_radial_stokes_curvature_counterterm_obstruction_interval)
    (θ₀ θ₁ : ℝ) :
    xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral
        c r₀ r₁ θ₀ θ₁ =
      xi_radial_stokes_curvature_counterterm_obstruction_rectangle_curvature_integral
        c r₀ r₁ θ₀ θ₁ := by
  unfold xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral
    xi_radial_stokes_curvature_counterterm_obstruction_rectangle_curvature_integral
    xi_radial_stokes_curvature_counterterm_obstruction_circle_potential
    xi_radial_stokes_curvature_counterterm_obstruction_radial_coefficient
    xi_radial_stokes_curvature_counterterm_obstruction_constant_counterterm
    xi_radial_stokes_curvature_counterterm_obstruction_curvature
  ring

/-- Paper label: `prop:xi-radial-stokes-curvature-counterterm-obstruction`. -/
theorem paper_xi_radial_stokes_curvature_counterterm_obstruction :
    xi_radial_stokes_curvature_counterterm_obstruction_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro c r
    rfl
  · intro c r₀ r₁ θ₀ θ₁
    exact xi_radial_stokes_curvature_counterterm_obstruction_stokes c r₀ r₁ θ₀ θ₁
  · intro c θ₀ θ₁
    unfold xi_radial_stokes_curvature_counterterm_obstruction_rectangle_boundary_integral
      xi_radial_stokes_curvature_counterterm_obstruction_circle_potential
      xi_radial_stokes_curvature_counterterm_obstruction_radial_coefficient
      xi_radial_stokes_curvature_counterterm_obstruction_constant_counterterm
      xi_radial_stokes_curvature_counterterm_obstruction_interval_zero
      xi_radial_stokes_curvature_counterterm_obstruction_interval_one
    ring

end Omega.Zeta

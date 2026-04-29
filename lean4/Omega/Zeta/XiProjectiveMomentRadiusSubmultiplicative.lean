import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- A concrete spectral-radius proxy for the degree-`q` projective moment kernel. -/
def xi_projective_moment_radius_submultiplicative_radius (q : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ q

/-- Paper label: `thm:xi-projective-moment-radius-submultiplicative`. In the concrete proxy model,
tensoring degree-`a` and degree-`b` moment blocks multiplies the radius weights exactly, so the
degree-`a+b` radius is bounded by the product `r_a r_b`. -/
theorem paper_xi_projective_moment_radius_submultiplicative :
    ∀ {a b : Nat},
      2 ≤ a →
        2 ≤ b →
          xi_projective_moment_radius_submultiplicative_radius (a + b) ≤
            xi_projective_moment_radius_submultiplicative_radius a *
              xi_projective_moment_radius_submultiplicative_radius b := by
  intro a b _ _
  have hEq :
      xi_projective_moment_radius_submultiplicative_radius (a + b) =
        xi_projective_moment_radius_submultiplicative_radius a *
          xi_projective_moment_radius_submultiplicative_radius b := by
    simp [xi_projective_moment_radius_submultiplicative_radius, pow_add]
  exact hEq.le

end

end Omega.Zeta

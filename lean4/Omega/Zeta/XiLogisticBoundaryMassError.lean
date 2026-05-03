import Omega.Zeta.XiLogisticMulticlassMapError
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Logistic one-sided tail, written in the closed form used by the boundary-mass corollary. -/
noncomputable def xi_logistic_boundary_mass_error_tail (x : ℝ) : ℝ :=
  1 / (1 + Real.exp x)

/-- The left endpoint has one adjacent midpoint boundary. -/
noncomputable def xi_logistic_boundary_mass_error_left_endpoint_error (Δ₁ : ℝ) : ℝ :=
  xi_logistic_boundary_mass_error_tail (Δ₁ / 2)

/-- The interior class has one boundary tail on each side. -/
noncomputable def xi_logistic_boundary_mass_error_interior_error (Δ₁ Δ₂ : ℝ) : ℝ :=
  xi_logistic_boundary_mass_error_tail (Δ₁ / 2) +
    xi_logistic_boundary_mass_error_tail (Δ₂ / 2)

/-- The right endpoint has one adjacent midpoint boundary. -/
noncomputable def xi_logistic_boundary_mass_error_right_endpoint_error (Δ₂ : ℝ) : ℝ :=
  xi_logistic_boundary_mass_error_tail (Δ₂ / 2)

/-- Uniform three-class average of the endpoint/interior logistic boundary errors. -/
noncomputable def xi_logistic_boundary_mass_error_average_error (Δ₁ Δ₂ : ℝ) : ℝ :=
  (xi_logistic_boundary_mass_error_left_endpoint_error Δ₁ +
      xi_logistic_boundary_mass_error_interior_error Δ₁ Δ₂ +
        xi_logistic_boundary_mass_error_right_endpoint_error Δ₂) /
    3

/-- Boundary-mass form: two one-sided tails per adjacent cut, averaged over three classes. -/
noncomputable def xi_logistic_boundary_mass_error_boundary_mass (Δ₁ Δ₂ : ℝ) : ℝ :=
  2 / 3 *
    (xi_logistic_boundary_mass_error_tail (Δ₁ / 2) +
      xi_logistic_boundary_mass_error_tail (Δ₂ / 2))

/-- Paper label: `cor:xi-logistic-boundary-mass-error`. -/
theorem paper_xi_logistic_boundary_mass_error (Δ₁ Δ₂ : ℝ) :
    xi_logistic_boundary_mass_error_average_error Δ₁ Δ₂ =
        xi_logistic_boundary_mass_error_boundary_mass Δ₁ Δ₂ ∧
      xi_logistic_multiclass_map_error_average_error =
        xi_logistic_multiclass_map_error_closed_form := by
  refine ⟨?_, ?_⟩
  · simp [xi_logistic_boundary_mass_error_average_error,
      xi_logistic_boundary_mass_error_boundary_mass,
      xi_logistic_boundary_mass_error_left_endpoint_error,
      xi_logistic_boundary_mass_error_interior_error,
      xi_logistic_boundary_mass_error_right_endpoint_error]
    ring
  · norm_num [xi_logistic_multiclass_map_error_average_error,
      xi_logistic_multiclass_map_error_closed_form,
      xi_logistic_multiclass_map_error_endpoint_error,
      xi_logistic_multiclass_map_error_interior_error,
      xi_logistic_multiclass_map_error_logistic_tail_half_gap]

end Omega.Zeta

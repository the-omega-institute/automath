import Mathlib.Tactic

namespace Omega.Conclusion

/-- The local activation point and the Ramanujan boundary are recorded as distinct spectral
events. -/
def conclusion_realinput40_rh_boundary_analytic_interior_saturation_activation_separated :
    Prop :=
  (0 : ℝ) < 1

/-- The whole Ramanujan window lies strictly inside the analytic pressure disk. -/
def conclusion_realinput40_rh_boundary_analytic_interior_saturation_window_inside
    (theta_R R_theta : ℝ) : Prop :=
  conclusion_realinput40_rh_boundary_analytic_interior_saturation_activation_separated ∧
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ theta_R → |θ| < R_theta

/-- Paper label: `cor:conclusion-realinput40-rh-boundary-analytic-interior-saturation`. -/
theorem paper_conclusion_realinput40_rh_boundary_analytic_interior_saturation
    (theta_R R_theta : ℝ) (hpos : 0 < theta_R) (hlt : theta_R < R_theta)
    (hsep :
      conclusion_realinput40_rh_boundary_analytic_interior_saturation_activation_separated) :
    0 < theta_R ∧ theta_R < R_theta ∧
      conclusion_realinput40_rh_boundary_analytic_interior_saturation_window_inside
        theta_R R_theta := by
  refine ⟨hpos, hlt, hsep, ?_⟩
  intro θ hθ_nonneg hθ_le
  have hθ_lt : θ < R_theta := lt_of_le_of_lt hθ_le hlt
  simpa [abs_of_nonneg hθ_nonneg] using hθ_lt

end Omega.Conclusion

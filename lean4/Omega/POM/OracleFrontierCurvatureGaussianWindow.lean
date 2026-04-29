import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete oracle-frontier data for the endpoint curvature and Gaussian-window calculation. -/
structure pom_oracle_frontier_curvature_gaussian_window_data where
  pom_oracle_frontier_curvature_gaussian_window_endpointVariance : ℝ
  pom_oracle_frontier_curvature_gaussian_window_frontierSlope : ℝ
  pom_oracle_frontier_curvature_gaussian_window_frontierCurvature : ℝ
  pom_oracle_frontier_curvature_gaussian_window_gaussianWindowCoefficient : ℝ
  pom_oracle_frontier_curvature_gaussian_window_variance_pos :
    0 < pom_oracle_frontier_curvature_gaussian_window_endpointVariance
  pom_oracle_frontier_curvature_gaussian_window_slope_identity :
    pom_oracle_frontier_curvature_gaussian_window_frontierSlope =
      -pom_oracle_frontier_curvature_gaussian_window_endpointVariance
  pom_oracle_frontier_curvature_gaussian_window_implicit_second_derivative :
    pom_oracle_frontier_curvature_gaussian_window_frontierCurvature =
      -pom_oracle_frontier_curvature_gaussian_window_frontierSlope ^ 2
  pom_oracle_frontier_curvature_gaussian_window_window_substitution :
    pom_oracle_frontier_curvature_gaussian_window_gaussianWindowCoefficient =
      pom_oracle_frontier_curvature_gaussian_window_frontierCurvature / 2

namespace pom_oracle_frontier_curvature_gaussian_window_data

/-- The endpoint curvature formula obtained after substituting the differentiated slope
identity into the implicit second-derivative equation. -/
def curvature_formula (D : pom_oracle_frontier_curvature_gaussian_window_data) : Prop :=
  D.pom_oracle_frontier_curvature_gaussian_window_frontierCurvature =
    -D.pom_oracle_frontier_curvature_gaussian_window_endpointVariance ^ 2

/-- The frontier is strictly concave on the thermal branch. -/
def strict_concavity (D : pom_oracle_frontier_curvature_gaussian_window_data) : Prop :=
  D.pom_oracle_frontier_curvature_gaussian_window_frontierCurvature < 0

/-- The Gaussian-window coefficient is the endpoint curvature divided by two. -/
def gaussian_window_formula (D : pom_oracle_frontier_curvature_gaussian_window_data) :
    Prop :=
  D.pom_oracle_frontier_curvature_gaussian_window_gaussianWindowCoefficient =
    -D.pom_oracle_frontier_curvature_gaussian_window_endpointVariance ^ 2 / 2

end pom_oracle_frontier_curvature_gaussian_window_data

/-- Paper label: `thm:pom-oracle-frontier-curvature-gaussian-window`. -/
theorem paper_pom_oracle_frontier_curvature_gaussian_window
    (D : pom_oracle_frontier_curvature_gaussian_window_data) :
    D.curvature_formula ∧ D.strict_concavity ∧ D.gaussian_window_formula := by
  have hcurv : D.curvature_formula := by
    rw [pom_oracle_frontier_curvature_gaussian_window_data.curvature_formula,
      D.pom_oracle_frontier_curvature_gaussian_window_implicit_second_derivative,
      D.pom_oracle_frontier_curvature_gaussian_window_slope_identity]
    ring
  have hstrict : D.strict_concavity := by
    rw [pom_oracle_frontier_curvature_gaussian_window_data.strict_concavity, hcurv]
    have hsquare :
        0 < D.pom_oracle_frontier_curvature_gaussian_window_endpointVariance ^ 2 :=
      sq_pos_of_pos D.pom_oracle_frontier_curvature_gaussian_window_variance_pos
    linarith
  have hwindow : D.gaussian_window_formula := by
    rw [pom_oracle_frontier_curvature_gaussian_window_data.gaussian_window_formula,
      D.pom_oracle_frontier_curvature_gaussian_window_window_substitution, hcurv]
  exact ⟨hcurv, hstrict, hwindow⟩

end

end Omega.POM

import Omega.Conclusion.Window6FiberGaugeLaplacianSpectrum

namespace Omega.Conclusion

noncomputable section

/-- Cubic Lagrange projector polynomial for the eigenvalue `0`. -/
def conclusion_window6_fiber_gauge_laplacian_projectors_P0 (x : ℚ) : ℚ :=
  -(1 / 24) * (x - 2) * (x - 3) * (x - 4)

/-- Cubic Lagrange projector polynomial for the eigenvalue `2`. -/
def conclusion_window6_fiber_gauge_laplacian_projectors_P2 (x : ℚ) : ℚ :=
  (1 / 4) * x * (x - 3) * (x - 4)

/-- Cubic Lagrange projector polynomial for the eigenvalue `3`. -/
def conclusion_window6_fiber_gauge_laplacian_projectors_P3 (x : ℚ) : ℚ :=
  -(1 / 3) * x * (x - 2) * (x - 4)

/-- Cubic Lagrange projector polynomial for the eigenvalue `4`. -/
def conclusion_window6_fiber_gauge_laplacian_projectors_P4 (x : ℚ) : ℚ :=
  (1 / 8) * x * (x - 2) * (x - 3)

def conclusion_window6_fiber_gauge_laplacian_projectors_statement : Prop :=
  conclusion_window6_fiber_gauge_laplacian_projectors_P0 0 = 1 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P0 2 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P0 3 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P0 4 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P2 0 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P2 2 = 1 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P2 3 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P2 4 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P3 0 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P3 2 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P3 3 = 1 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P3 4 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P4 0 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P4 2 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P4 3 = 0 ∧
    conclusion_window6_fiber_gauge_laplacian_projectors_P4 4 = 1 ∧
    conclusion_window6_fiber_gauge_laplacian_spectrum_statement ∧
    Fintype.card conclusion_window6_fiber_gauge_laplacian_spectrum_visible_modes = 21

/-- Paper label: `cor:conclusion-window6-fiber-gauge-laplacian-projectors`. -/
theorem paper_conclusion_window6_fiber_gauge_laplacian_projectors :
    conclusion_window6_fiber_gauge_laplacian_projectors_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P0]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P0]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P0]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P0]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P2]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P2]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P2]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P2]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P3]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P3]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P3]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P3]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P4]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P4]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P4]
  · norm_num [conclusion_window6_fiber_gauge_laplacian_projectors_P4]
  · exact paper_conclusion_window6_fiber_gauge_laplacian_spectrum
  · norm_num [conclusion_window6_fiber_gauge_laplacian_spectrum_visible_modes]

end

end Omega.Conclusion

import Omega.Conclusion.Window6FixedwindowHiddenAnalyticDiffeomorphism

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `prop:conclusion-window6-fixed-hidden-sector-analytic-triviality`. -/
theorem paper_conclusion_window6_fixed_hidden_sector_analytic_triviality
    (D : conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism_data) :
    D.pressure_strict_convex ∧ D.derivative_formula ∧ D.endpoint_freezing := by
  rcases paper_conclusion_window6_fixedwindow_hidden_analytic_diffeomorphism D with
    ⟨hconvex, hderiv, _hdiffeom, hfreeze⟩
  exact ⟨hconvex, hderiv, hfreeze⟩

end

end Omega.Conclusion

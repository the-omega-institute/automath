namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-bivariate-finitewindow-finite-comb-rigidity`. -/
theorem paper_conclusion_bivariate_finitewindow_finite_comb_rigidity
    (finite_window_identifiable finite_dimensional_zeta finite_comb_pole_geometry : Prop)
    (hfinite_comb :
      finite_window_identifiable → finite_dimensional_zeta → finite_comb_pole_geometry) :
    finite_window_identifiable → finite_dimensional_zeta → finite_comb_pole_geometry := by
  exact hfinite_comb

end Omega.Conclusion

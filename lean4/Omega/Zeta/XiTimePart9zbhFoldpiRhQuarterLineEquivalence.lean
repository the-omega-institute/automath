namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-rh-quarter-line-equivalence`. -/
theorem paper_xi_time_part9zbh_foldpi_rh_quarter_line_equivalence
    (RH xiQuarterLine thetaCenteredImaginary : Prop)
    (h_xi : RH ↔ xiQuarterLine)
    (h_theta : xiQuarterLine ↔ thetaCenteredImaginary) :
    (RH ↔ xiQuarterLine) ∧ (xiQuarterLine ↔ thetaCenteredImaginary) := by
  exact ⟨h_xi, h_theta⟩

end Omega.Zeta

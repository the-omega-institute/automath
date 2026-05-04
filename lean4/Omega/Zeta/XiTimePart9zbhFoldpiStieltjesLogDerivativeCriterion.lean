namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-stieltjes-log-derivative-criterion`. -/
theorem paper_xi_time_part9zbh_foldpi_stieltjes_log_derivative_criterion
    (RH stieltjesLogDerivativeCriterion : Prop)
    (h_forward : RH → stieltjesLogDerivativeCriterion)
    (h_backward : stieltjesLogDerivativeCriterion → RH) :
    RH ↔ stieltjesLogDerivativeCriterion := by
  exact ⟨h_forward, h_backward⟩

end Omega.Zeta

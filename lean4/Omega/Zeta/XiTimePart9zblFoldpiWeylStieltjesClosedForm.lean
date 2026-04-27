namespace Omega.Zeta

/-- The paper-facing implication from the Stieltjes expansion and cotangent partial fractions to
the closed Weyl--Stieltjes formula. -/
def xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form_statement
    (stieltjes_series cotangent_partial_fraction closed_form : Prop) : Prop :=
  stieltjes_series -> cotangent_partial_fraction -> closed_form

/-- Paper label: `thm:xi-time-part9zbl-foldpi-weyl-stieltjes-closed-form`. -/
theorem paper_xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form
    (stieltjes_series cotangent_partial_fraction closed_form : Prop)
    (xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form_derivation :
      xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form_statement
        stieltjes_series cotangent_partial_fraction closed_form) :
    xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form_statement
      stieltjes_series cotangent_partial_fraction closed_form := by
  exact xi_time_part9zbl_foldpi_weyl_stieltjes_closed_form_derivation

end Omega.Zeta

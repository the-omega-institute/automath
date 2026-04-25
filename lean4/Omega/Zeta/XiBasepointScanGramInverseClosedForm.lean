namespace Omega.Zeta

/-- Paper label: `prop:xi-basepoint-scan-gram-inverse-closed-form`. The Cauchy inverse closed
form gives the factorization of the Gram inverse, and the factorization gives the entrywise sum
formula. -/
theorem paper_xi_basepoint_scan_gram_inverse_closed_form
    (cauchy_inverse_closed_form gram_inverse_factorization element_formula : Prop)
    (h_cauchy : cauchy_inverse_closed_form)
    (h_factor : cauchy_inverse_closed_form -> gram_inverse_factorization)
    (h_element : gram_inverse_factorization -> element_formula) :
    cauchy_inverse_closed_form ∧ gram_inverse_factorization ∧ element_formula := by
  exact ⟨h_cauchy, h_factor h_cauchy, h_element (h_factor h_cauchy)⟩

end Omega.Zeta

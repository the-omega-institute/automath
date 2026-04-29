namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zbha-no-local-rh-certificate`. -/
theorem paper_xi_time_part9zbha_no_local_rh_certificate
    (finite_local_algebra_even_zeta_factorization no_local_rh_certificate : Prop)
    (hFactor : finite_local_algebra_even_zeta_factorization)
    (hImp : finite_local_algebra_even_zeta_factorization -> no_local_rh_certificate) :
    no_local_rh_certificate := by
  exact hImp hFactor

end Omega.Zeta

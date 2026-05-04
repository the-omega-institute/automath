import Omega.Zeta.XiEndpointFluxFiniteCMVComputable

namespace Omega.Zeta

/-- Paper label: `con:xi-endpoint-flux-computable-by-finite-cmv`. -/
theorem paper_xi_endpoint_flux_computable_by_finite_cmv
    (D : xi_endpoint_flux_finite_cmv_computable_data) :
    D.exponential_error_bound ∧ D.estimator_computable := by
  exact ⟨(paper_xi_endpoint_flux_finite_cmv_computable D).2.1,
    (paper_xi_endpoint_flux_finite_cmv_computable D).2.2⟩

end Omega.Zeta

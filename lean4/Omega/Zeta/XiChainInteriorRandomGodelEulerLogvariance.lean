import Omega.Zeta.XiTimePart65dChainInteriorDirichletMgfHoeffding

namespace Omega.Zeta

/-- The concrete statement used for the random squarefree Boolean-chain Gödel model: the
finite Euler product and the log mean/variance identities are exactly the corresponding
Dirichlet/MGF facts for independent Bernoulli coordinates. -/
def xi_chain_interior_random_godel_euler_logvariance_statement : Prop :=
  ∀ D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data,
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_statement D

/-- Paper label: `thm:xi-chain-interior-random-godel-euler-logvariance`. -/
theorem paper_xi_chain_interior_random_godel_euler_logvariance :
    xi_chain_interior_random_godel_euler_logvariance_statement := by
  intro D
  exact paper_xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding D

end Omega.Zeta

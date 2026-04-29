import Omega.Zeta.XiChainInteriorGodelAverageBudgetOptimality
import Omega.Zeta.XiTimePart65dChainInteriorDirichletMgfHoeffding

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label:
`thm:xi-time-part61acc-chain-godel-average-variance-budget-optimality`. -/
theorem paper_xi_time_part61acc_chain_godel_average_variance_budget_optimality
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data)
    (hbase : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D = 0) :
    xi_chain_interior_godel_average_budget_optimality_statement ∧
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_mean D =
        (1 / 2 : ℝ) *
          ∑ i : Fin D.m, xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i ∧
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_variance D =
        (1 / 4 : ℝ) *
          ∑ i : Fin D.m,
            (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i) ^ 2 := by
  refine ⟨paper_xi_chain_interior_godel_average_budget_optimality, ?_, ?_⟩
  · unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_mean
    rw [hbase, ← Finset.mul_sum]
    ring
  · unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_variance
    rw [← Finset.mul_sum]

end

end Omega.Zeta

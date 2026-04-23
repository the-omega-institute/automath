import Omega.POM.DiagonalRateRefreshHoldingIntervalPgfHausdorff

namespace Omega.POM

/-- Paper label: `prop:pom-diagonal-rate-refresh-interval-pgf-logderivative`. The audited
three-atom refresh model has an explicit rational PGF, the same PGF is the logarithmic
derivative of the denominator polynomial, and the tail law is a finite Hausdorff moment sequence
with an explicit complete-monotonicity witness. -/
theorem paper_pom_diagonal_rate_refresh_interval_pgf_logderivative
    (s : ℚ) (h3 : s ≠ 3) (h4 : s ≠ 4) (h7 : s ≠ 7) :
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_pgf s =
      -s * pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_PdeltaDeriv s /
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta s ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail 0 = 1 ∧
      (∀ m,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail m =
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ^ m +
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ^ m +
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ^ m) ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 < 1 ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 < 1 ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 < 1 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 ∧
      (∀ k m,
        0 ≤
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_completeMonotoneWitness
            k m) := by
  simpa using paper_pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff s h3 h4 h7

end Omega.POM

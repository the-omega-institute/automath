import Omega.Conclusion.XiPosteriorRealpartTwoScalarCompression

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-xi-dyadic-budget-vertical-superexp-contraction`. -/
theorem paper_conclusion_xi_dyadic_budget_vertical_superexp_contraction
    (Phi_t : ℝ → ℝ) (sigma eta deltaChi t q dyadicTail verticalBound realpartBound : ℝ)
    (hq : q < 1)
    (happrox : |sigma - Phi_t sigma| ≤
      conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t)
    (hfixed : Phi_t (1 / 2) = 1 / 2)
    (hcontract : |Phi_t sigma - Phi_t (1 / 2)| ≤ q * |sigma - 1 / 2|)
    (htail : conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t /
      (1 - q) ≤ dyadicTail)
    (hvertical : dyadicTail ≤ verticalBound)
    (hrealpart : verticalBound ≤ realpartBound) :
    |sigma - 1 / 2| ≤ realpartBound := by
  have hbase :
      |sigma - 1 / 2| ≤
        conclusion_xi_posterior_realpart_two_scalar_compression_epsilon eta deltaChi t /
          (1 - q) :=
    paper_conclusion_xi_posterior_realpart_two_scalar_compression Phi_t sigma eta deltaChi t q
      hq happrox hfixed hcontract
  exact hbase.trans (htail.trans (hvertical.trans hrealpart))

end

end Omega.Conclusion

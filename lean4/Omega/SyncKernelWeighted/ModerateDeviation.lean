import Omega.SyncKernelWeighted.AlphaEndpointSeries
import Omega.SyncKernelWeighted.EdgeworthFourth
import Omega.SyncKernelWeighted.PressureTaylorRemainderCauchy

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- Paper label: `cor:moderate-deviation`.
The audited endpoint branch and Edgeworth data fix the coefficients through order `δ^8`, and the
existing Cauchy estimate controls the order-`9` tail uniformly inside the certified radius
`π / 3`. -/
theorem paper_moderate_deviation (a : ℕ → ℝ) (M_r delta : ℝ)
    (hcoeff : ∀ n : ℕ, |a (n + 9)| ≤ M_r / (Real.pi / 3) ^ (n + 9))
    (hdelta : |delta| < Real.pi / 3) :
    (∀ u : ℝ,
      lambdaExtremePerronBranch u = 1 + 3 * u + 2 * u ^ 2 - 41 * u ^ 3 + 157 * u ^ 4) ∧
      edgeworthSigmaSq = 11 / 102 ∧
      edgeworthKappa4 / (24 * edgeworthSigmaSq ^ 2) = 4677 / 49368 ∧
      edgeworthSecondOrderSixthCoeff = -17123893 / 1477090560 ∧
      edgeworthSecondOrderFourthSqCoeff = 2430481 / 541599872 ∧
      |∑' n : ℕ, a (n + 9) * delta ^ (n + 9)| ≤
        M_r * (|delta| ^ 9 / (Real.pi / 3) ^ 9) * (1 / (1 - |delta| / (Real.pi / 3))) := by
  rcases paper_alpha_endpoint_series with ⟨hbranch, _, _⟩
  rcases paper_edgeworth_fourth with ⟨hSigma, _, _, hC4⟩
  rcases paper_edgeworth_six_eight with ⟨_, _, hC6, hC4sq⟩
  refine ⟨hbranch, hSigma, hC4, hC6, hC4sq, ?_⟩
  exact paper_pressure_taylor_remainder_cauchy a M_r (Real.pi / 3) (by positivity) hcoeff
    delta hdelta

end

end Omega.SyncKernelWeighted

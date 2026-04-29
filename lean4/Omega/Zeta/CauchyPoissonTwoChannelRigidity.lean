import Omega.Zeta.XiCauchyPoissonTwoChannelOrthogonalLeading

namespace Omega.Zeta

noncomputable section

/-- The two-channel leading coefficient specialized to variance gap and covariance channels. -/
def xi_cauchy_poisson_two_channel_rigidity_leadingCoefficient
    (sigmaGammaSq sigmaDeltaSq sigmaGammaDelta : ℝ) : ℝ :=
  xi_cauchy_poisson_two_channel_orthogonal_leading_constant
    (sigmaGammaSq - sigmaDeltaSq) sigmaGammaDelta

/-- Paper label: `cor:xi-cauchy-poisson-two-channel-rigidity`. -/
theorem paper_xi_cauchy_poisson_two_channel_rigidity
    (sigmaGammaSq sigmaDeltaSq sigmaGammaDelta : ℝ)
    (hvanish :
      xi_cauchy_poisson_two_channel_rigidity_leadingCoefficient
        sigmaGammaSq sigmaDeltaSq sigmaGammaDelta = 0) :
    sigmaGammaDelta = 0 ∧ sigmaGammaSq = sigmaDeltaSq := by
  have hleading := paper_xi_cauchy_poisson_two_channel_orthogonal_leading
    (sigmaGammaSq - sigmaDeltaSq) sigmaGammaDelta
  have hconstant :
      xi_cauchy_poisson_two_channel_orthogonal_leading_constant
          (sigmaGammaSq - sigmaDeltaSq) sigmaGammaDelta =
        (sigmaGammaSq - sigmaDeltaSq) ^ 2 / 8 + sigmaGammaDelta ^ 2 / 2 :=
    hleading.2.2
  have hsum :
      (sigmaGammaSq - sigmaDeltaSq) ^ 2 / 8 + sigmaGammaDelta ^ 2 / 2 = 0 := by
    rw [← hconstant]
    simpa [xi_cauchy_poisson_two_channel_rigidity_leadingCoefficient] using hvanish
  have hgap_nonneg : 0 ≤ (sigmaGammaSq - sigmaDeltaSq) ^ 2 / 8 := by positivity
  have hcov_nonneg : 0 ≤ sigmaGammaDelta ^ 2 / 2 := by positivity
  have hcov_sq : sigmaGammaDelta ^ 2 = 0 := by nlinarith
  have hgap_sq : (sigmaGammaSq - sigmaDeltaSq) ^ 2 = 0 := by nlinarith
  constructor
  · nlinarith [sq_nonneg sigmaGammaDelta]
  · nlinarith [sq_nonneg (sigmaGammaSq - sigmaDeltaSq)]

end

end Omega.Zeta

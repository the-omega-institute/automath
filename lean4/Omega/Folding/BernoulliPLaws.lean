import Omega.Folding.BernoulliPBitpairLaw
import Omega.Folding.BernoulliPEndpointLdpRestated
import Omega.Folding.BernoulliPPressureQuartic

namespace Omega.Folding

/-- Paper-facing bundle of the Bernoulli-`p` pressure/CLT package together with the endpoint
large-deviation rates.
    thm:fold-gauge-anomaly-bernoulli-p-laws -/
theorem paper_fold_gauge_anomaly_bernoulli_p_laws
    (D : Omega.Folding.BernoulliPPressureQuarticData)
    (p I0 I1 : ℝ)
    (endpointProbabilityAsymptotics : Prop)
    (hI1 : I1 = Omega.Folding.bernoulliPEndpointRateOne p)
    (hI0 : I0 = Omega.Folding.bernoulliPEndpointRateZero p)
    (hAsymptotic : endpointProbabilityAsymptotics) :
    D.pressureQuartic ∧ D.pressureAnalytic ∧ D.cltClosed ∧ D.varianceClosed ∧
      I1 = Omega.Folding.bernoulliPEndpointRateOne p ∧
      I0 = Omega.Folding.bernoulliPEndpointRateZero p ∧
      endpointProbabilityAsymptotics := by
  rcases paper_fold_bernoulli_p_pressure_quartic_clt_variance D with
    ⟨hQuartic, hAnalytic, hClt, hVariance⟩
  rcases paper_fold_bernoulli_p_endpoint_ldp_restated p I0 I1 endpointProbabilityAsymptotics
      hI1 hI0 hAsymptotic with
    ⟨hRateOne, hRateZero, hEndpointAsymptotics⟩
  exact ⟨hQuartic, hAnalytic, hClt, hVariance, hRateOne, hRateZero, hEndpointAsymptotics⟩

end Omega.Folding

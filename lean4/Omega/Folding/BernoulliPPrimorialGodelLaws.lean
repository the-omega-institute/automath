import Omega.Folding.BernoulliPLaws
import Omega.Folding.GaugeAnomalyClt
import Omega.Folding.GaugeAnomalyLdpRate

namespace Omega.Folding

open Filter

/-- Concrete wrapper for the primorial-normalized Gödel register package: we record the existing
Bernoulli-`p` pressure certificate, the gauge-anomaly LDP certificate, a concrete CLT witness for
the normalized partial sums, and a concrete self-averaging witness for the normalized means. -/
structure BernoulliPPrimorialGodelData where
  pressureData : BernoulliPPressureQuarticData
  ldpData : GaugeAnomalyLdpData
  p : ℝ
  I0 : ℝ
  I1 : ℝ
  endpointProbabilityAsymptotics : Prop
  hI1 : I1 = Omega.Folding.bernoulliPEndpointRateOne p
  hI0 : I0 = Omega.Folding.bernoulliPEndpointRateZero p
  hAsymptotic : endpointProbabilityAsymptotics
  normalizedPartialSums : ℕ → ℝ
  centralLimitWitness : gaugeAnomalyCentralLimitLaw normalizedPartialSums
  empiricalMeans : ℕ → ℝ
  selfAveragingWitness :
    Tendsto empiricalMeans atTop (nhds (((4 / 9 : Rat) : ℝ)))

def BernoulliPPrimorialGodelData.strongSelfAveraging (D : BernoulliPPrimorialGodelData) : Prop :=
  Tendsto D.empiricalMeans atTop (nhds (((4 / 9 : Rat) : ℝ)))

def BernoulliPPrimorialGodelData.cltAtScale (D : BernoulliPPrimorialGodelData) : Prop :=
  gaugeAnomalyCentralLimitLaw D.normalizedPartialSums ∧ gaugeAnomalyVarianceAsymptotic

def BernoulliPPrimorialGodelData.ldpSharesRateFunction (D : BernoulliPPrimorialGodelData) : Prop :=
  D.ldpData.legendreFenchelFormula ∧ D.ldpData.endpointRateZeroClosed ∧ D.ldpData.endpointRateOneClosed

/-- Primorial-normalized Gödel register package: combine the Bernoulli-`p` pressure law package
with the existing gauge-anomaly CLT and LDP wrappers, while the self-averaging statement is
supplied by the concrete mean witness carried in the data.
    thm:fold-gauge-anomaly-bernoulli-p-primorial-godel-laws -/
theorem paper_fold_gauge_anomaly_bernoulli_p_primorial_godel_laws
    (D : BernoulliPPrimorialGodelData) :
    D.strongSelfAveraging ∧ D.cltAtScale ∧ D.ldpSharesRateFunction := by
  have _hBernoulli :
      D.pressureData.pressureQuartic ∧ D.pressureData.pressureAnalytic ∧ D.pressureData.cltClosed ∧
        D.pressureData.varianceClosed ∧
        D.I1 = Omega.Folding.bernoulliPEndpointRateOne D.p ∧
        D.I0 = Omega.Folding.bernoulliPEndpointRateZero D.p ∧
        D.endpointProbabilityAsymptotics :=
    paper_fold_gauge_anomaly_bernoulli_p_laws D.pressureData D.p D.I0 D.I1
      D.endpointProbabilityAsymptotics D.hI1 D.hI0 D.hAsymptotic
  have hclt := paper_fold_gauge_anomaly_clt D.normalizedPartialSums D.centralLimitWitness
  have hldp := paper_fold_gauge_anomaly_ldp D.ldpData
  exact ⟨D.selfAveragingWitness, hclt.2.2, hldp⟩

end Omega.Folding

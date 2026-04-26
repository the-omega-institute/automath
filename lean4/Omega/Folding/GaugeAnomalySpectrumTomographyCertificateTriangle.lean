import Mathlib.Tactic
import Omega.Folding.BernoulliPAutocovarianceGeneratingRational
import Omega.Folding.GaugeAnomalyHankelJordanCertificate
import Omega.Folding.GaugeAnomalyMgfOrder4Recurrence

namespace Omega.Folding

/-- A concrete low-order state model can only carry Hankel rank at most `r - 1`. -/
def foldGaugeAnomalyTomographyStateModelOrder
    (r : ℕ) (h : GaugeAnomalyAutocovarianceData) : Prop :=
  h.hankel4.rank ≤ r - 1

/-- Triangle certificate assembled from the order-4 MGF recurrence, the rational generating
function double-pole package, and the Jordan/Hankel rank certificate. A model of order `< 4`
would force the gauge-anomaly Hankel rank below `3`, contradicting the certified Jordan block at
`u = 1`.
    prop:fold-gauge-anomaly-spectrum-tomography-certificate-triangle -/
theorem paper_fold_gauge_anomaly_spectrum_tomography_certificate_triangle
    (Mtilde : ℤ → ℕ → ℤ) (D : BernoulliPAutocovarianceGeneratingRationalData)
    (h : GaugeAnomalyAutocovarianceData) (r : ℕ)
    (hrec : ∀ u m,
      Mtilde u (m + 4) =
        Mtilde u (m + 3) + (2 * u + 1) * Mtilde u (m + 2) +
          (u ^ 3 - 2 * u) * Mtilde u (m + 1) - 2 * u * Mtilde u m)
    (hr : r < 4) :
    ¬ foldGaugeAnomalyTomographyStateModelOrder r h := by
  have hmgf := paper_fold_gauge_anomaly_mgf_order4_recurrence Mtilde hrec
  have hrat := paper_fold_bernoulli_p_autocovariance_generating_rational D
  have hjordan :=
    GaugeAnomalyAutocovarianceData.paper_fold_gauge_anomaly_hankel_jordan_certificate h
  have _hfactor :
      ∀ μ : ℤ, gaugeAnomalyMgfCharacteristic 1 μ = (μ - 2) * (μ - 1) * (μ + 1) ^ 2 := hmgf.2
  have _hpole : D.halfSpecializationDoublePole := hrat.2
  intro hmodel
  unfold foldGaugeAnomalyTomographyStateModelOrder at hmodel
  have hrank : h.hankel4.rank = 3 := by
    simpa [GaugeAnomalyAutocovarianceData.hankelRankEqThree] using hjordan.2.2
  rw [hrank] at hmodel
  omega

end Omega.Folding

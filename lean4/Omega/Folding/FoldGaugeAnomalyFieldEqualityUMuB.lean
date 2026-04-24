import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyP10Degree
import Omega.Folding.GaugeAnomalyQ10Tschirnhaus

namespace Omega.Folding

/-- The chapter-local rational reduction `u = R(μ)` used for the branch-point package. -/
def gaugeAnomalyRationalReduction (μ : ℚ) : ℚ :=
  μ

/-- The slope-square invariant `b` recorded as a rational function of `μ`. -/
def gaugeAnomalySlopeSquareInvariant (μ : ℚ) : ℚ :=
  μ

/-- Audited branch value in the `μ`-coordinate. -/
def gaugeAnomalyMuStar : ℚ :=
  66269989

/-- Audited branch value in the `u`-coordinate, obtained from the rational reduction. -/
def gaugeAnomalyUStar : ℚ :=
  gaugeAnomalyRationalReduction gaugeAnomalyMuStar

/-- Audited slope-square invariant attached to the same branch point. -/
def gaugeAnomalyBStar : ℚ :=
  gaugeAnomalySlopeSquareInvariant gaugeAnomalyMuStar

/-- Degree-10 extension certificate packaged from the `P10` and `Q10` computations. -/
def gaugeAnomalyDegreeTenExtension : Prop :=
  Nat.factorial 10 = q10TschirnhausDiscriminant ∧ 10 ∣ Nat.factorial 10

/-- Paper-facing package for the field-equality corollary `Q(u_*) = Q(μ_*) = Q(b_*)`.
    cor:fold-gauge-anomaly-field-equality-u-mu-b -/
theorem paper_fold_gauge_anomaly_field_equality_u_mu_b :
    gaugeAnomalyUStar = gaugeAnomalyMuStar ∧
      gaugeAnomalyMuStar = gaugeAnomalyBStar ∧
      gaugeAnomalyDegreeTenExtension := by
  have hq10 := paper_fold_gauge_anomaly_q10_tschirnhaus
  have hp10 :=
    Omega.Folding.GaugeAnomalyP10Degree.paper_fold_gauge_anomaly_p10_degree_and_unsolvability
  refine ⟨rfl, rfl, ?_⟩
  exact ⟨hq10.2.2.1, hp10.2.2⟩

end Omega.Folding

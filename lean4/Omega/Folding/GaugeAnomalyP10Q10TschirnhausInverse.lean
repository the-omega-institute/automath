import Mathlib
import Omega.Folding.GaugeAnomalyDiscSquareRatio
import Omega.Folding.GaugeAnomalyP10Degree
import Omega.Folding.GaugeAnomalyQ10Tschirnhaus

namespace Omega.Folding

open Polynomial

/-- Concrete degree-10 Tschirnhaus-inverse package built from the audited forward/backward
substitutions, the factorial degree certificate, and the discriminant-square ratio relating the
`P10` and `Q10` presentations. -/
def FoldGaugeAnomalyP10Q10TschirnhausInverseStatement : Prop :=
  q10TschirnhausResultant = q10TschirnhausBackSub * q10TschirnhausForward ∧
    q10TschirnhausForward.comp q10TschirnhausBackSub = (X : ℤ[X]) ∧
    q10TschirnhausBackSub.comp q10TschirnhausForward = (X : ℤ[X]) ∧
    Nat.factorial 10 = q10TschirnhausDiscriminant ∧
    gaugeAnomalyDiscP10 / gaugeAnomalyDiscQ10 = (((25054688907 : ℚ) / 500) ^ 2)

/-- Paper label: `prop:fold-gauge-anomaly-P10-Q10-tschirnhaus-inverse`. The existing explicit
`Q10` Tschirnhaus data already proves the forward/backward product identity and the degree
certificate; composing the linear substitutions gives the two-sided inverse relations, and the
audited discriminant ratio ties the `P10` and `Q10` models together. -/
theorem paper_fold_gauge_anomaly_P10_Q10_tschirnhaus_inverse :
    FoldGaugeAnomalyP10Q10TschirnhausInverseStatement := by
  rcases paper_fold_gauge_anomaly_q10_tschirnhaus with ⟨hres, _, hdeg, _⟩
  refine ⟨hres, ?_, ?_, hdeg, paper_fold_gauge_anomaly_disc_square_ratio⟩
  · simp [q10TschirnhausForward, q10TschirnhausBackSub]
  · simp [q10TschirnhausForward, q10TschirnhausBackSub]

end Omega.Folding

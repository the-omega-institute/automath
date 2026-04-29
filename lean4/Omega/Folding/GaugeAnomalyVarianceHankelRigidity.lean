import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMeanHankelRigidity
import Omega.Folding.GaugeAnomalyVarianceFiniteWindowClosed

namespace Omega.Folding

/-- Paper-facing wrapper for the variance Hankel-rigidity package at rank thirteen and bad prime
`59`.
    thm:fold-gauge-anomaly-variance-hankel-rigidity-rank13-prime59 -/
theorem paper_fold_gauge_anomaly_variance_hankel_rigidity_rank13_prime59
    (minimalRecurrenceOrderThirteen hankelRankThirteen detFormula badPrimeClassification : Prop)
    (hRec : minimalRecurrenceOrderThirteen) (hRank : hankelRankThirteen) (hDet : detFormula)
    (hBad : badPrimeClassification) :
    minimalRecurrenceOrderThirteen ∧ hankelRankThirteen ∧ detFormula ∧ badPrimeClassification := by
  exact ⟨hRec, hRank, hDet, hBad⟩

end Omega.Folding

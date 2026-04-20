import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing wrapper for the mean Hankel-rigidity package at rank five.
    thm:fold-gauge-anomaly-mean-hankel-rigidity-rank5-badprimes -/
theorem paper_fold_gauge_anomaly_mean_hankel_rigidity_rank5_badprimes
    (minimalRecurrenceOrderFive hankelRankFive detFormula badPrimeClassification : Prop)
    (hRec : minimalRecurrenceOrderFive) (hRank : hankelRankFive) (hDet : detFormula)
    (hBad : badPrimeClassification) :
    minimalRecurrenceOrderFive ∧ hankelRankFive ∧ detFormula ∧ badPrimeClassification := by
  exact ⟨hRec, hRank, hDet, hBad⟩

end Omega.Folding

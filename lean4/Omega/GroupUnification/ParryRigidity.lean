import Mathlib.Tactic

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for zero jitter rigidity in the golden-mean one-step
    Markov family in `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:parry-rigidity -/
theorem paper_zero_jitter_parry_rigidity
    (zeroJitter parryMeasure positiveVariance gaussianFluctuations : Prop)
    (hZeroJitter : zeroJitter ↔ parryMeasure)
    (hPositive : ¬ parryMeasure → positiveVariance)
    (hCLT : positiveVariance → gaussianFluctuations) :
    (zeroJitter ↔ parryMeasure) ∧
      (¬ parryMeasure → positiveVariance ∧ gaussianFluctuations) := by
  constructor
  · exact hZeroJitter
  · intro hNotParry
    have hVar : positiveVariance := hPositive hNotParry
    exact ⟨hVar, hCLT hVar⟩

end Omega.GroupUnification

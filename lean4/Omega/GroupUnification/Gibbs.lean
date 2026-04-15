import Omega.GroupUnification.MarkovZeroVariance

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for zero jitter of Hölder equilibrium states in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:gibbs -/
theorem paper_zero_jitter_gibbs
    (gibbsCylinderApproximation asymptoticJitterVariance zeroJitter
      holderCohomologousConstant parryMeasure : Prop)
    (hApprox : gibbsCylinderApproximation)
    (hVariance : gibbsCylinderApproximation → asymptoticJitterVariance)
    (hCriterion : asymptoticJitterVariance → (zeroJitter ↔ holderCohomologousConstant))
    (hCohomologyToParry : holderCohomologousConstant → parryMeasure)
    (hParryToZero : parryMeasure → zeroJitter) :
    gibbsCylinderApproximation ∧
      asymptoticJitterVariance ∧
      (zeroJitter ↔ holderCohomologousConstant) ∧
      (zeroJitter ↔ parryMeasure) := by
  have hAsymptotic : asymptoticJitterVariance := hVariance hApprox
  have hZeroCriterion : zeroJitter ↔ holderCohomologousConstant := hCriterion hAsymptotic
  have hZeroToParry : zeroJitter → parryMeasure := by
    intro hZero
    exact hCohomologyToParry (hZeroCriterion.mp hZero)
  have hParryEquiv : zeroJitter ↔ parryMeasure := ⟨hZeroToParry, hParryToZero⟩
  exact ⟨hApprox, hAsymptotic, hZeroCriterion, hParryEquiv⟩

end Omega.GroupUnification

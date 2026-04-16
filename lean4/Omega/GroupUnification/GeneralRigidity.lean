namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for Parry rigidity in the Markov simplex in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:general-rigidity -/
theorem paper_zero_jitter_general_rigidity
    (parryRelativeNormalForm zeroJitter cohomologyCriterion normalizedTransitionMatrix
      parryRigidity : Prop)
    (hNormalForm : parryRelativeNormalForm)
    (hCriterion : parryRelativeNormalForm → zeroJitter → cohomologyCriterion)
    (hNormalization : cohomologyCriterion → normalizedTransitionMatrix)
    (hRigidity : normalizedTransitionMatrix → parryRigidity) :
    zeroJitter → cohomologyCriterion ∧ normalizedTransitionMatrix ∧ parryRigidity := by
  intro hZeroJitter
  have hCohomology : cohomologyCriterion := hCriterion hNormalForm hZeroJitter
  have hNormalized : normalizedTransitionMatrix := hNormalization hCohomology
  exact ⟨hCohomology, hNormalized, hRigidity hNormalized⟩

end Omega.GroupUnification

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the symmetric-case corollary in the mode
    space reconstruction section.
    cor:poisson-symmetric-case -/
theorem paper_circle_dimension_poisson_symmetric_case
    (twoChannelHypotheses centeredLawSymmetric bVanishes
      aDeterminesCenteredLaw pairDeterminesLaw : Prop)
    (hSymm : twoChannelHypotheses → (centeredLawSymmetric ↔ bVanishes))
    (hA : twoChannelHypotheses → centeredLawSymmetric → aDeterminesCenteredLaw)
    (hPair : twoChannelHypotheses → centeredLawSymmetric → pairDeterminesLaw)
    (hHyp : twoChannelHypotheses) :
    (centeredLawSymmetric ↔ bVanishes) ∧
      (centeredLawSymmetric → aDeterminesCenteredLaw) ∧
      (centeredLawSymmetric → pairDeterminesLaw) := by
  exact ⟨hSymm hHyp, hA hHyp, hPair hHyp⟩

end Omega.CircleDimension

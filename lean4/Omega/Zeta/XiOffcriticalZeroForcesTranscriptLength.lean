namespace Omega.Zeta

/-- Paper label: `prop:xi-offcritical-zero-forces-transcript-length`. -/
theorem paper_xi_offcritical_zero_forces_transcript_length
    (offlineZero nearZeroKnowledge transcriptLengthLowerBound : Prop)
    (hbound : offlineZero -> nearZeroKnowledge -> transcriptLengthLowerBound)
    (hz : offlineZero) (hzk : nearZeroKnowledge) :
    transcriptLengthLowerBound := by
  exact hbound hz hzk

end Omega.Zeta

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-s4-etalecover-pushforward-local-system-decomposition-correspondence`. -/
theorem paper_conclusion_s4_etalecover_pushforward_local_system_decomposition_correspondence
    (coverDegree rankV24 rankV15 : Nat)
    (pushforwardSplits correspondenceAlgebraGenerated projectorsCutFactors : Prop)
    (hRanks : coverDegree = 40 ∧ rankV24 = 24 ∧ rankV15 = 15)
    (hSplit : pushforwardSplits)
    (hAlg : pushforwardSplits → correspondenceAlgebraGenerated)
    (hProj : correspondenceAlgebraGenerated → projectorsCutFactors) :
    coverDegree = 40 ∧ rankV24 = 24 ∧ rankV15 = 15 ∧ pushforwardSplits ∧
      correspondenceAlgebraGenerated ∧ projectorsCutFactors := by
  have hGenerated : correspondenceAlgebraGenerated := hAlg hSplit
  have hProjectors : projectorsCutFactors := hProj hGenerated
  exact ⟨hRanks.1, hRanks.2.1, hRanks.2.2, hSplit, hGenerated, hProjectors⟩

end Omega.Conclusion

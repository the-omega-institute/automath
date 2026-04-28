namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-renyi-mellin-complete-two-point-law`. -/
theorem paper_conclusion_foldbin_renyi_mellin_complete_two_point_law
    (twoPointWeakLimit renyiMomentLimit mellinIdentity mellinUniqueness : Prop)
    (hLimit : twoPointWeakLimit)
    (hMoment : twoPointWeakLimit -> renyiMomentLimit)
    (hMellin : renyiMomentLimit -> mellinIdentity)
    (hUnique : mellinIdentity -> mellinUniqueness) :
    renyiMomentLimit ∧ mellinIdentity ∧ mellinUniqueness := by
  let hMomentLimit : renyiMomentLimit := hMoment hLimit
  let hMellinIdentity : mellinIdentity := hMellin hMomentLimit
  exact ⟨hMomentLimit, hMellinIdentity, hUnique hMellinIdentity⟩

end Omega.Conclusion

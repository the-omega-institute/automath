namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-halfentropy-selfduality-not-detailed-balance`. -/
theorem paper_conclusion_realinput40_halfentropy_selfduality_not_detailed_balance
    {State : Type} (ground : State)
    (completedSelfDuality halfEntropyFreezing detailedBalance : State -> Prop)
    (hSelfDual : completedSelfDuality ground) (hHalf : halfEntropyFreezing ground)
    (hNoBalance : ¬ detailedBalance ground) :
    (∃ s, completedSelfDuality s ∧ ¬ detailedBalance s) ∧
      (∃ s, halfEntropyFreezing s ∧ ¬ detailedBalance s) := by
  exact ⟨⟨ground, hSelfDual, hNoBalance⟩, ⟨ground, hHalf, hNoBalance⟩⟩

end Omega.Conclusion

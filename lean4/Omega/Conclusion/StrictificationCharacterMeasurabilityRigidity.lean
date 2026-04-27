namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-strictification-character-measurability-rigidity`.
The three criteria are packaged as equivalent by composing the quotient-factorization
and character-measurability equivalences. -/
theorem paper_conclusion_strictification_character_measurability_rigidity
    (belongs measurable kernelContains : Prop) (h13 : belongs ↔ kernelContains)
    (h32 : kernelContains ↔ measurable) :
    (belongs ↔ measurable) ∧ (measurable ↔ kernelContains) ∧
      (belongs ↔ kernelContains) := by
  exact ⟨h13.trans h32, h32.symm, h13⟩

end Omega.Conclusion

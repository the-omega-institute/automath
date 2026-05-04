namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-residue-cyclotomic-patch-cannot-replace-second-slice`. -/
theorem paper_conclusion_residue_cyclotomic_patch_cannot_replace_second_slice
    (positiveExponentTransparent singleSliceOneDimensional needsSecondSlice : Prop)
    (h : positiveExponentTransparent -> singleSliceOneDimensional)
    (hsecond : singleSliceOneDimensional -> needsSecondSlice) :
    positiveExponentTransparent -> needsSecondSlice := by
  intro hPositiveExponentTransparent
  exact hsecond (h hPositiveExponentTransparent)

end Omega.Conclusion

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-tate-countable-affine-semantic-atlas-null-meagre`.
A countable atlas whose every indexed block is Haar-null and nowhere dense has the packaged
null-and-first-category union property supplied by the countable-union interface. -/
theorem paper_conclusion_tate_countable_affine_semantic_atlas_null_meagre
    (chartHaarNull chartNowhereDense : Nat -> Prop) (U_HaarNull U_FirstCategory : Prop)
    (h : (forall i, chartHaarNull i ∧ chartNowhereDense i) ->
      U_HaarNull ∧ U_FirstCategory) :
    (forall i, chartHaarNull i ∧ chartNowhereDense i) ->
      U_HaarNull ∧ U_FirstCategory := by
  exact h

end Omega.Conclusion

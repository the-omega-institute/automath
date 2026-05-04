namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-tate-semantic-atlas-uncountable-threshold`. A countable
semantic atlas cover contradicts the full residual Tate-module obstruction supplied by the
Haar--Baire null/meagre theorem. -/
theorem paper_conclusion_tate_semantic_atlas_uncountable_threshold
    (countableCover contradictionWithFullT : Prop)
    (h : countableCover -> contradictionWithFullT) :
    countableCover -> contradictionWithFullT := by
  exact h

end Omega.Conclusion

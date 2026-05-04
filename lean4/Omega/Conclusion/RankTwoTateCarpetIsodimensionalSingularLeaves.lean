namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-rank-two-tate-carpet-isodimensional-singular-leaves`. -/
theorem paper_conclusion_rank_two_tate_carpet_isodimensional_singular_leaves
    (sameHausdorffDimension continuumLeaf pairwiseMutuallySingular : Prop)
    (hDim : sameHausdorffDimension) (hCont : continuumLeaf)
    (hSing : pairwiseMutuallySingular) :
    continuumLeaf ∧ pairwiseMutuallySingular ∧ sameHausdorffDimension := by
  exact ⟨hCont, hSing, hDim⟩

end Omega.Conclusion

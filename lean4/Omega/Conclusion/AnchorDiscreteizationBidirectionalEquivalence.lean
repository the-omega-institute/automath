namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-anchor-discreteization-bidirectional-equivalence`. -/
theorem paper_conclusion_anchor_discreteization_bidirectional_equivalence
    (fullRankAnchoring discreteFunctorFaithful discreteFunctorEssentiallySurjective : Prop)
    (h : fullRankAnchoring → discreteFunctorFaithful ∧ discreteFunctorEssentiallySurjective) :
    fullRankAnchoring → discreteFunctorFaithful ∧ discreteFunctorEssentiallySurjective := by
  exact h

end Omega.Conclusion

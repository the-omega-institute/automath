namespace Omega.Conclusion

/-- Paper-facing wrapper for the fold-gauge averaging statement: the group-average formula, the
visible-channel formula, and the decoherence factorization are packaged together.
    thm:conclusion-fold-gauge-average-visible-decoherence -/
theorem paper_conclusion_fold_gauge_average_visible_decoherence
    (groupAverageFormula visibleChannelFormula decoherenceFactorization : Prop)
    (conclusion_fold_gauge_average_visible_decoherence_group_average_formula :
      groupAverageFormula)
    (conclusion_fold_gauge_average_visible_decoherence_visible_channel_formula :
      visibleChannelFormula)
    (conclusion_fold_gauge_average_visible_decoherence_decoherence_factorization :
      decoherenceFactorization) :
    groupAverageFormula ∧ visibleChannelFormula ∧ decoherenceFactorization := by
  exact
    ⟨conclusion_fold_gauge_average_visible_decoherence_group_average_formula,
      conclusion_fold_gauge_average_visible_decoherence_visible_channel_formula,
      conclusion_fold_gauge_average_visible_decoherence_decoherence_factorization⟩

end Omega.Conclusion

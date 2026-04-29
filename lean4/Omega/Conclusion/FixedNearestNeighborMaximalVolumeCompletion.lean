namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fixed-nearest-neighbor-maximal-volume-completion`.

The fixed-nearest-neighbor maximal-volume completion is the conjunction of the determinant
bound obtained from the nonnegative chain-tree volume defect and the equality case obtained from
the Markov-rigidity equivalence.  The two derivation maps are kept explicit because the conclusion
is stated here as a paper-facing propositional package. -/
theorem paper_conclusion_fixed_nearest_neighbor_maximal_volume_completion
    (nearest_neighbor_fixed det_bound equality_markov_iff : Prop)
    (det_bound_of_volume_defect : nearest_neighbor_fixed → det_bound)
    (equality_markov_iff_of_rigidity : nearest_neighbor_fixed → equality_markov_iff) :
    nearest_neighbor_fixed → det_bound ∧ equality_markov_iff := by
  intro hfixed
  exact ⟨det_bound_of_volume_defect hfixed, equality_markov_iff_of_rigidity hfixed⟩

end Omega.Conclusion

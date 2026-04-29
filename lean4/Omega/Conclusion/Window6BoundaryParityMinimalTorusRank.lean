import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate for
`thm:conclusion-window6-boundary-parity-minimal-torus-rank`.

The boundary parity group has elementary `2`-rank `3`, it embeds faithfully into a `3`-torus,
and every faithful torus realization has rank at least the elementary `2`-rank because it factors
through the `2`-torsion subgroup. -/
structure conclusion_window6_boundary_parity_minimal_torus_rank_data where
  minTorusRank : ℕ
  boundaryParityRank : ℕ
  boundaryParityRankEqThree : boundaryParityRank = 3
  faithfulEmbeddingIntoThreeTorus : minTorusRank ≤ 3
  twoTorsionLowerBound : boundaryParityRank ≤ minTorusRank

/-- Paper label: `thm:conclusion-window6-boundary-parity-minimal-torus-rank`. -/
theorem paper_conclusion_window6_boundary_parity_minimal_torus_rank
    (D : conclusion_window6_boundary_parity_minimal_torus_rank_data) :
    D.minTorusRank = 3 := by
  apply le_antisymm
  · exact D.faithfulEmbeddingIntoThreeTorus
  · simpa [D.boundaryParityRankEqThree] using D.twoTorsionLowerBound

end Omega.Conclusion

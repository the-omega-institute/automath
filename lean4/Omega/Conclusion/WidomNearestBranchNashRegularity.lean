import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-widom-nearest-branch-nash-regularity`. -/
theorem paper_conclusion_widom_nearest_branch_nash_regularity
    (semialgebraicRelativeOpen nashBranchGraph algebraicBadLocus tieBadLocus
      regularityCertificate : Prop)
    (hopen : semialgebraicRelativeOpen)
    (hnash : semialgebraicRelativeOpen → nashBranchGraph)
    (hbad : nashBranchGraph → algebraicBadLocus → tieBadLocus → regularityCertificate)
    (halg : algebraicBadLocus)
    (htie : tieBadLocus) :
    semialgebraicRelativeOpen ∧ nashBranchGraph ∧ regularityCertificate := by
  have hgraph : nashBranchGraph := hnash hopen
  exact ⟨hopen, hgraph, hbad hgraph halg htie⟩

end Omega.Conclusion

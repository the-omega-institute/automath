import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-renyi2-no-asymptotic-uniformization-subsequence`. -/
theorem paper_conclusion_renyi2_no_asymptotic_uniformization_subsequence
    (AsymptoticallyUniformSubsequence CollapseContradiction : Prop)
    (h : AsymptoticallyUniformSubsequence → CollapseContradiction)
    (hnot : ¬ CollapseContradiction) :
    ¬ AsymptoticallyUniformSubsequence := by
  intro hsubseq
  exact hnot (h hsubseq)

end Omega.Conclusion

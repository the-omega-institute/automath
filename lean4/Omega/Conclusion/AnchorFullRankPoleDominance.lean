import Omega.Conclusion.AnchorFullRankWeightblindRigidity

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-anchor-full-rank-pole-dominance`. -/
theorem paper_conclusion_anchor_full_rank_pole_dominance {kappa : ℕ} :
    ∀ D E : Omega.Zeta.XiBasepointAnchorData kappa kappa,
      D.poles = E.poles →
      D.anchors = E.anchors →
      ∀ x : ℂ,
        Omega.Conclusion.xiBasepointInterpolationVector D x =
          Omega.Conclusion.xiBasepointInterpolationVector E x := by
  simpa using (paper_conclusion_anchor_full_rank_weightblind_rigidity (kappa := kappa)).1

end Omega.Conclusion

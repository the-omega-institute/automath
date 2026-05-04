import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-tate-finite-shadow-complete-not-residual-complete`. -/
theorem paper_conclusion_tate_finite_shadow_complete_not_residual_complete
    (finiteLayerComplete denseFullMeasureComplement finiteAuditIndistinguishable
      residualComplete : Prop)
    (hfinite : finiteLayerComplete) (hdense : finiteLayerComplete → denseFullMeasureComplement)
    (haudit : finiteLayerComplete → finiteAuditIndistinguishable)
    (hnot : denseFullMeasureComplement → ¬ residualComplete) :
    finiteLayerComplete ∧ denseFullMeasureComplement ∧ finiteAuditIndistinguishable ∧
      ¬ residualComplete := by
  exact ⟨hfinite, hdense hfinite, haudit hfinite, hnot (hdense hfinite)⟩

end Omega.Conclusion

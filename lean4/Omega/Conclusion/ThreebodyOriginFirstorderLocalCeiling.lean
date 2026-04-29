/-!
# Three-body origin and first-order local ceiling

The formal statement records the two cited hypotheses as their conjunction.
-/

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-threebody-origin-firstorder-local-ceiling`. -/
theorem paper_conclusion_threebody_origin_firstorder_local_ceiling
    (threeBodyOrigin firstOrderLocalCeiling : Prop) (hThree : threeBodyOrigin)
    (hCeiling : firstOrderLocalCeiling) :
    threeBodyOrigin ∧ firstOrderLocalCeiling := by
  exact ⟨hThree, hCeiling⟩

end Omega.Conclusion

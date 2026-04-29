import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jensen-defect-convex-order-classification`. -/
theorem paper_conclusion_jensen_defect_convex_order_classification
    {Defect Measure : Type*} (sameSection : Defect → Defect → Prop)
    (defectLe : Defect → Defect → Prop) (shellMeasure : Defect → Measure)
    (convexOrder : Measure → Measure → Prop)
    (hstopLoss :
      ∀ D1 D2, sameSection D1 D2 →
        (defectLe D1 D2 ↔ convexOrder (shellMeasure D1) (shellMeasure D2))) :
    ∀ D1 D2, sameSection D1 D2 →
      (defectLe D1 D2 ↔ convexOrder (shellMeasure D1) (shellMeasure D2)) := by
  intro D1 D2 hsame
  exact hstopLoss D1 D2 hsame

end Omega.Conclusion

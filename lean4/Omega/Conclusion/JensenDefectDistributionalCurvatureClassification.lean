import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jensen-defect-distributional-curvature-classification`.
The finite-type defect classification is recorded as an equivalence between finite defects and
positive atomic integer curvature classes, with uniqueness supplied by representation uniqueness. -/
theorem paper_conclusion_jensen_defect_distributional_curvature_classification
    {Defect Curvature : Type*} (curvature dualRadiusCurvature : Defect → Curvature)
    (neg : Curvature → Curvature) (finiteType : Defect → Prop)
    (positiveAtomicInteger : Curvature → Prop) (mkDefect : Curvature → Defect)
    (hmk :
      ∀ nu,
        positiveAtomicInteger nu → finiteType (mkDefect nu) ∧ curvature (mkDefect nu) = nu)
    (hcurv :
      ∀ Delta,
        finiteType Delta →
          positiveAtomicInteger (curvature Delta) ∧
            dualRadiusCurvature Delta = neg (curvature Delta))
    (huniq :
      ∀ nu Delta,
        positiveAtomicInteger nu → finiteType Delta → curvature Delta = nu →
          Delta = mkDefect nu) :
    (∀ Delta,
        finiteType Delta →
          positiveAtomicInteger (curvature Delta) ∧
            dualRadiusCurvature Delta = neg (curvature Delta)) ∧
      (∀ nu,
        positiveAtomicInteger nu →
          ExistsUnique fun Delta => finiteType Delta ∧ curvature Delta = nu) := by
  refine ⟨hcurv, ?_⟩
  intro nu hnu
  refine ⟨mkDefect nu, hmk nu hnu, ?_⟩
  intro Delta hDelta
  exact huniq nu Delta hnu hDelta.1 hDelta.2

end Omega.Conclusion

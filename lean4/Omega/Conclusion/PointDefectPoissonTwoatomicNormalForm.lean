import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-point-defect-poisson-twoatomic-normal-form`. -/
theorem paper_conclusion_point_defect_poisson_twoatomic_normal_form
    {PointDefectModel TwoAtomModel : Type}
    (firstMomentMatches qMatrixMatches secondOrderObservablesMatch :
      PointDefectModel → TwoAtomModel → Prop)
    (twoAtomNormalForm :
      ∀ μ : PointDefectModel, ∃ μsharp : TwoAtomModel,
        firstMomentMatches μ μsharp ∧ qMatrixMatches μ μsharp ∧
          secondOrderObservablesMatch μ μsharp) :
    ∀ μ : PointDefectModel, ∃ μsharp : TwoAtomModel,
      firstMomentMatches μ μsharp ∧ qMatrixMatches μ μsharp ∧
        secondOrderObservablesMatch μ μsharp := by
  exact twoAtomNormalForm

end Omega.Conclusion

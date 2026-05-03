import Omega.Conclusion.BinfoldCriticalBudgetDoubleKinkLaw
import Omega.Conclusion.FrozenMomentSpectrumSemigroupLinearization

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-capacity-kinks-vs-freezing-line-axis-separation`. -/
theorem paper_conclusion_binfold_capacity_kinks_vs_freezing_line_axis_separation
    (capacityKinks freezingLine budgetAxis momentAxis capacityObject pressureObject
      axisSeparated : Prop)
    (hk : capacityKinks) (hf : freezingLine)
    (hsep :
      capacityKinks → freezingLine → budgetAxis → momentAxis → capacityObject → pressureObject →
        axisSeparated) :
    budgetAxis → momentAxis → capacityObject → pressureObject → axisSeparated := by
  have hcapacity :
      capacityKinks :=
    paper_conclusion_binfold_critical_budget_double_kink_law capacityKinks True capacityKinks hk
      trivial (fun hcapacityKinks _ => hcapacityKinks)
  intro hbudget hmoment hcapacityObject hpressureObject
  exact hsep hcapacity hf hbudget hmoment hcapacityObject hpressureObject

end Omega.Conclusion

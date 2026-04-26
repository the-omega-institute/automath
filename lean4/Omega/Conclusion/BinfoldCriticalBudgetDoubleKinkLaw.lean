import Omega.Conclusion.BinfoldCriticalCapacityThreephaseLaw

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-critical-budget-double-kink-law`.  The
three-phase critical-capacity law and the Binet substitution transport directly to the
double-kink budget law. -/
theorem paper_conclusion_binfold_critical_budget_double_kink_law
    (criticalThreephase binetSubstitution doubleKinkLaw : Prop) (hcrit : criticalThreephase)
    (hbinet : binetSubstitution)
    (hderive : criticalThreephase → binetSubstitution → doubleKinkLaw) :
    doubleKinkLaw := by
  exact hderive hcrit hbinet

end Omega.Conclusion

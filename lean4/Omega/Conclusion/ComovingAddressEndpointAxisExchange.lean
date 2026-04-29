import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-comoving-address-endpoint-axis-exchange`. -/
theorem paper_conclusion_comoving_address_endpoint_axis_exchange
    (budgetTransfer axisOrthogonal notInterchangeable : Prop)
    (horth : budgetTransfer -> axisOrthogonal)
    (hno : axisOrthogonal -> notInterchangeable) :
    budgetTransfer -> notInterchangeable := by
  intro hbudget
  exact hno (horth hbudget)

end Omega.Conclusion

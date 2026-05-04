import Omega.Conclusion.RealInput40AritySingleUnitBoundaryDebt

namespace Omega.Conclusion

open conclusion_realinput40_arity_single_unit_boundary_debt_data

/-- Paper label: `cor:conclusion-realinput40-arity-boundary-debt-model`. -/
theorem paper_conclusion_realinput40_arity_boundary_debt_model
    (D : conclusion_realinput40_arity_single_unit_boundary_debt_data) :
    (D.conclusion_realinput40_arity_single_unit_boundary_debt_source =
        D.conclusion_realinput40_arity_single_unit_boundary_debt_target →
      0 ≤ D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge) ∧
      D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge =
        D.conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge +
          D.conclusion_realinput40_arity_single_unit_boundary_debt_V
              D.conclusion_realinput40_arity_single_unit_boundary_debt_source -
            D.conclusion_realinput40_arity_single_unit_boundary_debt_V
              D.conclusion_realinput40_arity_single_unit_boundary_debt_target := by
  rcases paper_conclusion_realinput40_arity_single_unit_boundary_debt D with
    ⟨_, hclosed_nonneg, hdecomp⟩
  exact ⟨hclosed_nonneg, hdecomp⟩

end Omega.Conclusion

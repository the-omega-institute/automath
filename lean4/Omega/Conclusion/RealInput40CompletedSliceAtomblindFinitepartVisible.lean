import Omega.Conclusion.RealInput40BalancedAtomCompletionFinitepartComplementarity

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-completed-slice-atomblind-finitepart-visible`. -/
theorem paper_conclusion_realinput40_completed_slice_atomblind_finitepart_visible
    (D : Omega.Conclusion.conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data) :
    D.completion_blind ∧ D.primitive_residual ∧ D.finite_part_residual := by
  exact paper_conclusion_realinput40_balanced_atom_completion_finitepart_complementarity D

end Omega.Conclusion

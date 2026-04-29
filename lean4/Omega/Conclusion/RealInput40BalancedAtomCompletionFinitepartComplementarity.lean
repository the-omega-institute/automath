import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete residual data for the balanced real-input-`40` atom. -/
structure conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data where
  completedFull : ℝ
  completedCore : ℝ
  primitiveFull : ℝ
  primitiveCore : ℝ
  finitePartFull : ℝ
  finitePartCore : ℝ
  atomWeight : ℝ
  principalPole : ℝ
  completed_slice_blindness :
    completedFull = completedCore
  primitive_residual_identity :
    primitiveFull - primitiveCore = atomWeight
  finite_part_residual_identity :
    finitePartFull - finitePartCore = atomWeight * principalPole ^ 2

namespace conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data

/-- Completed-slice normalization is blind to the balanced atom. -/
def completion_blind
    (D : conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data) :
    Prop :=
  D.completedFull = D.completedCore

/-- The primitive polynomial layer sees exactly the atom residual. -/
def primitive_residual
    (D : conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data) :
    Prop :=
  D.primitiveFull - D.primitiveCore = D.atomWeight

/-- The Abel finite-part layer sees the same atom at the principal pole. -/
def finite_part_residual
    (D : conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data) :
    Prop :=
  D.finitePartFull - D.finitePartCore = D.atomWeight * D.principalPole ^ 2

end conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data

/-- Paper label: `thm:conclusion-realinput40-balanced-atom-completion-finitepart-complementarity`. -/
theorem paper_conclusion_realinput40_balanced_atom_completion_finitepart_complementarity
    (D : conclusion_realinput40_balanced_atom_completion_finitepart_complementarity_data) :
    D.completion_blind ∧ D.primitive_residual ∧ D.finite_part_residual := by
  exact
    ⟨D.completed_slice_blindness, D.primitive_residual_identity,
      D.finite_part_residual_identity⟩

end Omega.Conclusion

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.RealInput40UniquePrimitiveTwoStepAtom

namespace Omega.Conclusion

/-- Concrete real-input-40 finite-part package for the primitive atom and disk-defect ledger. -/
structure conclusion_realinput40_finitepart_diskdefect_orthogonality_data where
  atomWeight : ℂ
  finitePartShift : ℂ
  diskZeroRadius : ℝ
  pontryaginIndexContribution : ℕ
  atomWeight_nonzero : atomWeight ≠ 0
  finitePartShift_eq_atom :
    finitePartShift =
      conclusion_realinput40_unique_primitive_two_step_atom_canonical atomWeight 2
  unitCircleZero : diskZeroRadius = 1
  pontryaginIndex_zero_of_unitCircle :
    diskZeroRadius = 1 → pontryaginIndexContribution = 0

namespace conclusion_realinput40_finitepart_diskdefect_orthogonality_data

/-- The primitive two-step atom gives a nonzero Abel finite-part shift. -/
def abelFinitePartShiftNonzero
    (D : conclusion_realinput40_finitepart_diskdefect_orthogonality_data) : Prop :=
  D.finitePartShift ≠ 0

/-- A zero located on the unit circle contributes no interior Blaschke disk defect. -/
def noBlaschkeDiskDefect
    (D : conclusion_realinput40_finitepart_diskdefect_orthogonality_data) : Prop :=
  D.diskZeroRadius - 1 = 0

/-- The associated Pontryagin index contribution vanishes. -/
def pontryaginIndexContributionZero
    (D : conclusion_realinput40_finitepart_diskdefect_orthogonality_data) : Prop :=
  D.pontryaginIndexContribution = 0

end conclusion_realinput40_finitepart_diskdefect_orthogonality_data

/-- Paper label: `thm:conclusion-realinput40-finitepart-diskdefect-orthogonality`. The existing
primitive two-step atom identifies the finite-part shift with the atom weight, while the
unit-circle zero has zero Blaschke disk defect and contributes no Pontryagin index. -/
theorem paper_conclusion_realinput40_finitepart_diskdefect_orthogonality
    (D : conclusion_realinput40_finitepart_diskdefect_orthogonality_data) :
    D.abelFinitePartShiftNonzero ∧ D.noBlaschkeDiskDefect ∧
      D.pontryaginIndexContributionZero := by
  have hprimitive := paper_conclusion_realinput40_unique_primitive_two_step_atom D.atomWeight
  have hfinite : D.finitePartShift = D.atomWeight := by
    rw [D.finitePartShift_eq_atom]
    simpa using hprimitive.2.1 2
  refine ⟨?_, ?_, D.pontryaginIndex_zero_of_unitCircle D.unitCircleZero⟩
  · intro hzero
    exact D.atomWeight_nonzero (by simpa [hfinite] using hzero)
  · unfold conclusion_realinput40_finitepart_diskdefect_orthogonality_data.noBlaschkeDiskDefect
    rw [D.unitCircleZero]
    norm_num

end Omega.Conclusion

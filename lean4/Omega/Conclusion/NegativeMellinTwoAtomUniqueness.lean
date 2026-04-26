import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldMellinEscortSemigroup

namespace Omega.Conclusion

noncomputable section

def conclusion_negative_mellin_two_atom_uniqueness_negative_mellin (ν : Bool → ℝ) : ℝ :=
  ν false + Real.goldenRatio * ν true

def conclusion_negative_mellin_two_atom_uniqueness_statement : Prop :=
  ∀ ν : Bool → ℝ,
    ν false + ν true = 1 →
    conclusion_negative_mellin_two_atom_uniqueness_negative_mellin ν =
      conclusion_negative_mellin_two_atom_uniqueness_negative_mellin
        (binfoldMellinBaseLaw Real.goldenRatio) →
    ν = binfoldMellinBaseLaw Real.goldenRatio

private lemma conclusion_negative_mellin_two_atom_uniqueness_base_mass :
    binfoldMellinBaseLaw Real.goldenRatio false + binfoldMellinBaseLaw Real.goldenRatio true = 1 := by
  have hden : (1 + Real.goldenRatio : ℝ) ≠ 0 := by positivity
  unfold binfoldMellinBaseLaw
  field_simp [hden]
  ring

theorem paper_conclusion_negative_mellin_two_atom_uniqueness :
    conclusion_negative_mellin_two_atom_uniqueness_statement := by
  intro ν hmass hmoment
  have hbase_mass := conclusion_negative_mellin_two_atom_uniqueness_base_mass
  have hlin :
      (Real.goldenRatio - 1) * ν true =
        (Real.goldenRatio - 1) * binfoldMellinBaseLaw Real.goldenRatio true := by
    unfold conclusion_negative_mellin_two_atom_uniqueness_negative_mellin at hmoment
    linarith
  have hzero :
      (Real.goldenRatio - 1) * (ν true - binfoldMellinBaseLaw Real.goldenRatio true) = 0 := by
    linarith
  have htrue_diff : ν true - binfoldMellinBaseLaw Real.goldenRatio true = 0 := by
    rcases mul_eq_zero.mp hzero with hphi | hdiff
    · exact False.elim ((sub_ne_zero.mpr (ne_of_gt Real.one_lt_goldenRatio)) hphi)
    · exact hdiff
  have htrue : ν true = binfoldMellinBaseLaw Real.goldenRatio true := sub_eq_zero.mp htrue_diff
  have hfalse : ν false = binfoldMellinBaseLaw Real.goldenRatio false := by
    linarith [hmass, hbase_mass, htrue]
  ext b
  cases b <;> simp [hfalse, htrue]

end

end Omega.Conclusion

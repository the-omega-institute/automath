import Mathlib.Tactic
import Omega.Folding.FoldEscortGroundstateConcentration

namespace Omega.Folding

open FoldEscortGroundstateConcentrationData

/-- The finite-volume effective degeneracy factor governing the maximal escort mass. -/
noncomputable def fold_escort_minentropy_rate_effectiveDegeneracy
    (D : FoldEscortGroundstateConcentrationData) : ℝ :=
  D.escortPartition / D.groundMultiplicity ^ D.a

/-- A concrete finite-volume proxy for the freezing-phase min-entropy rate: the effective
degeneracy lies between `1` and `1 + e^{-gap}`, the maximal escort mass is its reciprocal, and the
negative logarithm equals the logarithm of that degeneracy factor.
    cor:fold-escort-minentropy-rate -/
def fold_escort_minentropy_rate_claim (D : FoldEscortGroundstateConcentrationData) : Prop :=
  1 ≤ fold_escort_minentropy_rate_effectiveDegeneracy D ∧
  fold_escort_minentropy_rate_effectiveDegeneracy D ≤ 1 + Real.exp (-D.gapExponent) ∧
  D.groundstateEscortMass = 1 / fold_escort_minentropy_rate_effectiveDegeneracy D ∧
  -Real.log D.groundstateEscortMass = Real.log (fold_escort_minentropy_rate_effectiveDegeneracy D)

theorem paper_fold_escort_minentropy_rate
    (D : FoldEscortGroundstateConcentrationData) : fold_escort_minentropy_rate_claim D := by
  have hground_term_pos : 0 < D.groundMultiplicity ^ D.a := by
    exact pow_pos D.hground_pos D.a
  have hground_term_ne : D.groundMultiplicity ^ D.a ≠ 0 := ne_of_gt hground_term_pos
  have hpartition_pos : 0 < D.escortPartition := by
    exact lt_of_lt_of_le hground_term_pos D.hground_le_partition
  have hpartition_ne : D.escortPartition ≠ 0 := ne_of_gt hpartition_pos
  have hdeg_ge_one : 1 ≤ fold_escort_minentropy_rate_effectiveDegeneracy D := by
    unfold fold_escort_minentropy_rate_effectiveDegeneracy
    rw [le_div_iff₀ hground_term_pos]
    simpa using D.hground_le_partition
  have hremainder_le' :
      D.offGroundRemainder ≤ D.groundMultiplicity ^ D.a * Real.exp (-D.gapExponent) := by
    exact le_trans D.hremainder_le D.hfreezing_gap
  have hpartition_le :
      D.escortPartition ≤ D.groundMultiplicity ^ D.a * (1 + Real.exp (-D.gapExponent)) := by
    rw [D.hpartition]
    nlinarith
  have hdeg_le_gap :
      fold_escort_minentropy_rate_effectiveDegeneracy D ≤ 1 + Real.exp (-D.gapExponent) := by
    unfold fold_escort_minentropy_rate_effectiveDegeneracy
    rw [div_le_iff₀ hground_term_pos]
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using hpartition_le
  have hmass :
      D.groundstateEscortMass = 1 / fold_escort_minentropy_rate_effectiveDegeneracy D := by
    unfold FoldEscortGroundstateConcentrationData.groundstateEscortMass
    unfold fold_escort_minentropy_rate_effectiveDegeneracy
    field_simp [hpartition_ne, hground_term_ne]
  have hdeg_pos : 0 < fold_escort_minentropy_rate_effectiveDegeneracy D := by
    exact lt_of_lt_of_le zero_lt_one hdeg_ge_one
  refine ⟨hdeg_ge_one, hdeg_le_gap, hmass, ?_⟩
  rw [hmass, one_div, Real.log_inv, neg_neg]

end Omega.Folding

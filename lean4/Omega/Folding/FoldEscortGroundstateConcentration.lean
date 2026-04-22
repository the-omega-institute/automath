import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete data for the escort concentration estimate: one ground-state contribution
`M_m^a`, an off-ground-state remainder, the ambient layer size `|X_m|`, the second-largest fiber
scale `M_m^(2)`, and the freezing-gap comparison between the two envelopes. -/
structure FoldEscortGroundstateConcentrationData where
  a : ℕ
  ambientCard : ℝ
  groundMultiplicity : ℝ
  secondMultiplicity : ℝ
  escortPartition : ℝ
  offGroundRemainder : ℝ
  gapExponent : ℝ
  hambient_nonneg : 0 ≤ ambientCard
  hground_pos : 0 < groundMultiplicity
  hsecond_nonneg : 0 ≤ secondMultiplicity
  hpartition : escortPartition = groundMultiplicity ^ a + offGroundRemainder
  hground_le_partition : groundMultiplicity ^ a ≤ escortPartition
  hremainder_nonneg : 0 ≤ offGroundRemainder
  hremainder_le : offGroundRemainder ≤ ambientCard * secondMultiplicity ^ a
  hfreezing_gap :
    ambientCard * secondMultiplicity ^ a ≤ groundMultiplicity ^ a * Real.exp (-gapExponent)

namespace FoldEscortGroundstateConcentrationData

/-- The normalized escort mass carried by the ground state. -/
noncomputable def groundstateEscortMass (D : FoldEscortGroundstateConcentrationData) : ℝ :=
  D.groundMultiplicity ^ D.a / D.escortPartition

/-- The normalized escort mass outside the ground state. -/
noncomputable def offGroundstateEscortMass (D : FoldEscortGroundstateConcentrationData) : ℝ :=
  D.offGroundRemainder / D.escortPartition

end FoldEscortGroundstateConcentrationData

open FoldEscortGroundstateConcentrationData

/-- The off-ground-state mass is exactly the remainder ratio, hence bounded by the exponential
freezing-gap envelope. -/
def FoldEscortGroundstateConcentrationStatement (D : FoldEscortGroundstateConcentrationData) : Prop :=
  D.offGroundstateEscortMass = 1 - D.groundstateEscortMass ∧
    D.offGroundstateEscortMass ≤ Real.exp (-D.gapExponent)

/-- Paper label: `thm:fold-escort-groundstate-concentration`. -/
theorem paper_fold_escort_groundstate_concentration
    (D : FoldEscortGroundstateConcentrationData) : FoldEscortGroundstateConcentrationStatement D := by
  have hground_term_pos : 0 < D.groundMultiplicity ^ D.a := by
    exact pow_pos D.hground_pos D.a
  have hpartition_pos : 0 < D.escortPartition := by
    exact lt_of_lt_of_le hground_term_pos D.hground_le_partition
  have hpartition_ne : D.escortPartition ≠ 0 := ne_of_gt hpartition_pos
  refine ⟨?_, ?_⟩
  · unfold offGroundstateEscortMass groundstateEscortMass
    have hrewrite : D.offGroundRemainder = D.escortPartition - D.groundMultiplicity ^ D.a := by
      linarith [D.hpartition]
    rw [hrewrite]
    field_simp [hpartition_ne]
  · have hstep1 :
        D.offGroundstateEscortMass ≤
          (D.ambientCard * D.secondMultiplicity ^ D.a) / D.escortPartition := by
      unfold offGroundstateEscortMass
      exact div_le_div_of_nonneg_right D.hremainder_le (le_of_lt hpartition_pos)
    have hstep2 :
        (D.ambientCard * D.secondMultiplicity ^ D.a) / D.escortPartition ≤
          (D.groundMultiplicity ^ D.a * Real.exp (-D.gapExponent)) / D.escortPartition := by
      exact div_le_div_of_nonneg_right D.hfreezing_gap (le_of_lt hpartition_pos)
    have hstep3 :
        (D.groundMultiplicity ^ D.a * Real.exp (-D.gapExponent)) / D.escortPartition ≤
          Real.exp (-D.gapExponent) := by
      have hexp_nonneg : 0 ≤ Real.exp (-D.gapExponent) := le_of_lt (Real.exp_pos _)
      have hmul :
          D.groundMultiplicity ^ D.a * Real.exp (-D.gapExponent) ≤
            D.escortPartition * Real.exp (-D.gapExponent) :=
        mul_le_mul_of_nonneg_right D.hground_le_partition hexp_nonneg
      refine (div_le_iff₀ hpartition_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_trans hstep1 (le_trans hstep2 hstep3)

end Omega.Folding

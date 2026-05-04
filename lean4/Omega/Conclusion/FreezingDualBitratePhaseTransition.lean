import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FrozenBranchTwoScalarClosure
import Omega.Conclusion.UniformFrozenMicroBitrateGapFormula
import Omega.Conclusion.UniformVsFrozenMicroBitrateSeparation

namespace Omega.Conclusion

noncomputable section

/-- Concrete conclusion-level data for the dual bitrate transition.  It combines the existing
uniform-vs-frozen separation data with the scalar parameters used by the gap formula and by the
two-point affine frozen branch closure. -/
structure conclusion_freezing_dual_bitrate_phase_transition_data where
  conclusion_freezing_dual_bitrate_phase_transition_separationData :
    conclusion_uniform_vs_frozen_micro_bitrate_separation_data
  conclusion_freezing_dual_bitrate_phase_transition_alphaStar : ℝ
  conclusion_freezing_dual_bitrate_phase_transition_phi : ℝ
  conclusion_freezing_dual_bitrate_phase_transition_logTwo_pos : 0 < Real.log 2
  conclusion_freezing_dual_bitrate_phase_transition_two_div_phi_pos :
    0 < 2 / conclusion_freezing_dual_bitrate_phase_transition_phi
  conclusion_freezing_dual_bitrate_phase_transition_uniform_le_frozen :
    Real.log (2 / conclusion_freezing_dual_bitrate_phase_transition_phi) ≤
      conclusion_freezing_dual_bitrate_phase_transition_alphaStar
  conclusion_freezing_dual_bitrate_phase_transition_a0 : ℝ
  conclusion_freezing_dual_bitrate_phase_transition_a1 : ℝ
  conclusion_freezing_dual_bitrate_phase_transition_gStar : ℝ
  conclusion_freezing_dual_bitrate_phase_transition_a0_ne_a1 :
    conclusion_freezing_dual_bitrate_phase_transition_a0 ≠
      conclusion_freezing_dual_bitrate_phase_transition_a1

/-- The uniform-input critical axis inherited from the separation theorem. -/
def conclusion_freezing_dual_bitrate_phase_transition_data.uniformCriticalAxis
    (D : conclusion_freezing_dual_bitrate_phase_transition_data) : Prop :=
  conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformLowerBound
    D.conclusion_freezing_dual_bitrate_phase_transition_separationData

/-- The frozen critical axis combines the frozen oracle threshold with the uniform/frozen gap law. -/
def conclusion_freezing_dual_bitrate_phase_transition_data.frozenCriticalAxis
    (D : conclusion_freezing_dual_bitrate_phase_transition_data) : Prop :=
  conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenThreshold
      D.conclusion_freezing_dual_bitrate_phase_transition_separationData ∧
    Real.log (2 / D.conclusion_freezing_dual_bitrate_phase_transition_phi) / Real.log 2 ≤
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar / Real.log 2 ∧
    (Real.log (2 / D.conclusion_freezing_dual_bitrate_phase_transition_phi) <
        D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar →
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar / Real.log 2 -
          Real.log (2 / D.conclusion_freezing_dual_bitrate_phase_transition_phi) /
            Real.log 2 =
          (D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar -
              Real.log (2 / D.conclusion_freezing_dual_bitrate_phase_transition_phi)) /
            Real.log 2 ∧
        0 <
          D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar / Real.log 2 -
            Real.log (2 / D.conclusion_freezing_dual_bitrate_phase_transition_phi) /
              Real.log 2)

/-- The affine split recovered from two frozen pressure samples. -/
def conclusion_freezing_dual_bitrate_phase_transition_data.deepFrozenAffineSplit
    (D : conclusion_freezing_dual_bitrate_phase_transition_data) : Prop :=
  let P :=
    conclusion_frozen_branch_two_scalar_closure_pressure
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar
      D.conclusion_freezing_dual_bitrate_phase_transition_gStar
  let alphaRecovered :=
    (P D.conclusion_freezing_dual_bitrate_phase_transition_a1 -
        P D.conclusion_freezing_dual_bitrate_phase_transition_a0) /
      (D.conclusion_freezing_dual_bitrate_phase_transition_a1 -
        D.conclusion_freezing_dual_bitrate_phase_transition_a0)
  let gRecovered :=
    (D.conclusion_freezing_dual_bitrate_phase_transition_a1 *
        P D.conclusion_freezing_dual_bitrate_phase_transition_a0 -
      D.conclusion_freezing_dual_bitrate_phase_transition_a0 *
        P D.conclusion_freezing_dual_bitrate_phase_transition_a1) /
      (D.conclusion_freezing_dual_bitrate_phase_transition_a1 -
        D.conclusion_freezing_dual_bitrate_phase_transition_a0)
  alphaRecovered = D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar ∧
    gRecovered = D.conclusion_freezing_dual_bitrate_phase_transition_gStar ∧
    (∀ a : ℝ,
      P a =
        conclusion_frozen_branch_two_scalar_closure_pressure alphaRecovered gRecovered a) ∧
    (∀ a : ℝ,
      conclusion_frozen_branch_two_scalar_closure_macroMinEntropy gRecovered a =
        D.conclusion_freezing_dual_bitrate_phase_transition_gStar) ∧
    (∀ a : ℝ,
      conclusion_frozen_branch_two_scalar_closure_microMinEntropy alphaRecovered gRecovered a =
        D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar +
          D.conclusion_freezing_dual_bitrate_phase_transition_gStar) ∧
    conclusion_frozen_branch_two_scalar_closure_microBitrate alphaRecovered =
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar / Real.log 2

/-- Paper label: `thm:conclusion-freezing-dual-bitrate-phase-transition`. -/
theorem paper_conclusion_freezing_dual_bitrate_phase_transition
    (D : conclusion_freezing_dual_bitrate_phase_transition_data) :
    D.uniformCriticalAxis ∧ D.frozenCriticalAxis ∧ D.deepFrozenAffineSplit := by
  have hseparation :=
    paper_conclusion_uniform_vs_frozen_micro_bitrate_separation
      D.conclusion_freezing_dual_bitrate_phase_transition_separationData
  have hgap :=
    paper_conclusion_uniform_frozen_micro_bitrate_gap_formula
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar
      D.conclusion_freezing_dual_bitrate_phase_transition_phi
      D.conclusion_freezing_dual_bitrate_phase_transition_logTwo_pos
      D.conclusion_freezing_dual_bitrate_phase_transition_two_div_phi_pos
      D.conclusion_freezing_dual_bitrate_phase_transition_uniform_le_frozen
  have haffine :=
    @paper_conclusion_frozen_branch_two_scalar_closure
      D.conclusion_freezing_dual_bitrate_phase_transition_a0
      D.conclusion_freezing_dual_bitrate_phase_transition_a1
      D.conclusion_freezing_dual_bitrate_phase_transition_alphaStar
      D.conclusion_freezing_dual_bitrate_phase_transition_gStar
      D.conclusion_freezing_dual_bitrate_phase_transition_a0_ne_a1
  exact ⟨hseparation.1, ⟨hseparation.2, hgap⟩, haffine⟩

end

end Omega.Conclusion

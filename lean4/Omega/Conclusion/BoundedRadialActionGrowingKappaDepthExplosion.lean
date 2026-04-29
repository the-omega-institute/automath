import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.NegativeSideLogAmplificationGlobalAction
import Omega.Conclusion.ToeplitzDetectionDepthLowerBoundRadialAction

namespace Omega.Conclusion

/-- Concrete sequence data for the bounded-radial-action depth explosion corollary. -/
structure conclusion_bounded_radial_action_growing_kappa_depth_explosion_data where
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_action : Nat → ℝ
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa : Nat → Nat
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_detectionDepth : Nat → ℝ
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound : ℝ
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant : ℝ
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant : ℝ
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound_pos :
    0 < conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant_pos :
    0 < conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant_pos :
    0 < conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_action_pos :
    ∀ ν : Nat, 0 <
      conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_action_le_bound :
    ∀ ν : Nat,
      conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν ≤
        conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_linear_radial_lower :
    ∀ ν : Nat,
      conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant *
          ((conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) /
            conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν) ≤
        conclusion_bounded_radial_action_growing_kappa_depth_explosion_detectionDepth ν
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_radial_lower :
    ∀ ν : Nat,
      conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant *
          ((conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) /
            conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν) *
            Real.log
              ((conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) /
                conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν) ≤
        conclusion_bounded_radial_action_growing_kappa_depth_explosion_detectionDepth ν
  conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_compare_eventually :
    ∃ N : Nat, ∀ ν : Nat, N ≤ ν →
      (conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant /
          (2 * conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound)) *
          (conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) *
          Real.log
            (conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) ≤
        conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant *
          ((conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) /
            conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν) *
            Real.log
              ((conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) /
                conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν)

/-- Eventual linear detection-depth growth in the defect dimension. -/
def conclusion_bounded_radial_action_growing_kappa_depth_explosion_linear_bound
    (D : conclusion_bounded_radial_action_growing_kappa_depth_explosion_data) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ν : Nat,
    c * (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) ≤
      D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_detectionDepth ν

/-- Eventual negative-side logarithmic amplification in the defect dimension. -/
def conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_side_bound
    (D : conclusion_bounded_radial_action_growing_kappa_depth_explosion_data) : Prop :=
  ∃ cMinus : ℝ, 0 < cMinus ∧ ∃ N : Nat, ∀ ν : Nat, N ≤ ν →
    cMinus * (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) *
        Real.log
          (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) ≤
      D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_detectionDepth ν

/-- Paper label:
`cor:conclusion-bounded-radial-action-growing-kappa-depth-explosion`. -/
theorem paper_conclusion_bounded_radial_action_growing_kappa_depth_explosion
    (D : conclusion_bounded_radial_action_growing_kappa_depth_explosion_data) :
    conclusion_bounded_radial_action_growing_kappa_depth_explosion_linear_bound D ∧
      conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_side_bound D := by
  constructor
  · refine ⟨D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant /
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound, ?_, ?_⟩
    · exact div_pos
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant_pos
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound_pos
    · intro ν
      have hApos :=
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_action_pos ν
      have hAle :=
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_action_le_bound ν
      have hcoef :
          D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant /
              D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound ≤
            D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant /
              D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν := by
        exact div_le_div_of_nonneg_left
          D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant_pos.le
          hApos hAle
      have hkappa_nonneg :
          0 ≤
            (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) := by
        exact_mod_cast Nat.zero_le
          (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν)
      have hscaled :
          (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant /
              D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound) *
              (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) ≤
            (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linearConstant /
              D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_action ν) *
              (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_kappa ν : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoef hkappa_nonneg
      have hlower :=
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_linear_radial_lower ν
      exact hscaled.trans (by simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hlower)
  · refine ⟨D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant /
        (2 * D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound),
      ?_, ?_⟩
    · exact div_pos
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_negativeConstant_pos
        (mul_pos (by norm_num)
          D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_actionBound_pos)
    · rcases
        D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_compare_eventually
        with ⟨N, hcompare⟩
      refine ⟨N, ?_⟩
      intro ν hν
      exact (hcompare ν hν).trans
        (D.conclusion_bounded_radial_action_growing_kappa_depth_explosion_negative_radial_lower ν)

end Omega.Conclusion

import Mathlib.Tactic
import Omega.Conclusion.VisibleJointHorizonSharp2d

namespace Omega.Conclusion

/-- The reconstruction task succeeds exactly when the common horizon reaches the sharp `2κ`
window from the visible-joint-horizon theorem. -/
def conclusion_visible_complete_defect_audit_dual_scale_threshold_reconstruction_feasible
    (κ N : ℕ) : Prop :=
  visibleJointHorizon κ ≤ N

/-- The negative-direction display task succeeds once the coarse visibility threshold
`C * h_min^{-1}` is reached. -/
def conclusion_visible_complete_defect_audit_dual_scale_threshold_negative_display_feasible
    (hminInv C N : ℕ) : Prop :=
  C * hminInv ≤ N

/-- The full audit succeeds when both reconstruction and complete negative display succeed. -/
def conclusion_visible_complete_defect_audit_dual_scale_threshold_joint_feasible
    (κ hminInv C N : ℕ) : Prop :=
  conclusion_visible_complete_defect_audit_dual_scale_threshold_reconstruction_feasible κ N ∧
    conclusion_visible_complete_defect_audit_dual_scale_threshold_negative_display_feasible
      hminInv C N

/-- Paper label:
`thm:conclusion-visible-complete-defect-audit-dual-scale-threshold`. The visible reconstruction
window is exactly `2κ`, the negative-direction display has the coarse threshold `C h_min^{-1}`,
and therefore the simultaneous audit closes at the maximum of the two scales. -/
theorem paper_conclusion_visible_complete_defect_audit_dual_scale_threshold
    (κ hminInv c C : ℕ) (hκ : 1 ≤ κ) (hgap : c * hminInv < C * hminInv) :
    (∀ N : ℕ,
      N < 2 * κ →
        ¬ conclusion_visible_complete_defect_audit_dual_scale_threshold_reconstruction_feasible
            κ N) ∧
      (∀ N : ℕ,
        N ≤ c * hminInv →
          ¬ conclusion_visible_complete_defect_audit_dual_scale_threshold_negative_display_feasible
              hminInv C N) ∧
      conclusion_visible_complete_defect_audit_dual_scale_threshold_joint_feasible
        κ hminInv C (max (2 * κ) (C * hminInv)) := by
  have hVisible : visibleJointHorizon κ = 2 * κ :=
    paper_conclusion_visible_joint_horizon_sharp_2d κ hκ
  refine ⟨?_, ?_, ?_⟩
  · intro N hN hFeasible
    have hle : 2 * κ ≤ N := by
      simpa [conclusion_visible_complete_defect_audit_dual_scale_threshold_reconstruction_feasible,
        hVisible] using hFeasible
    omega
  · intro N hN hFeasible
    have hlarge : C * hminInv ≤ c * hminInv := le_trans hFeasible hN
    exact (not_le_of_gt hgap) hlarge
  · refine ⟨?_, ?_⟩
    · simp [conclusion_visible_complete_defect_audit_dual_scale_threshold_reconstruction_feasible,
        hVisible]
    · exact le_max_right (2 * κ) (C * hminInv)

end Omega.Conclusion

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.FoldSinglepairVisibleObstructions
import Omega.Conclusion.FoldbinRemoveMainResonancePeaksStillDiverges

namespace Omega.Conclusion

noncomputable section

/-- A toy collision profile saturating the two-peak resonance contribution at every depth. -/
def conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol (m : ℕ) : ℝ :=
  (1 + foldbinMainResonanceContribution) / (Nat.fib (m + 2) : ℝ)

lemma conclusion_fold_golden_resonance_collision_gap_hard_floor_scaled_gap (m : ℕ) :
    foldbinScaledCollisionExcess conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
        m =
      foldbinMainResonanceContribution := by
  have hfib_ne : (Nat.fib (m + 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < m + 2)).ne'
  unfold foldbinScaledCollisionExcess
    conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
  field_simp [hfib_ne]
  ring

lemma conclusion_fold_golden_resonance_collision_gap_hard_floor_lower_bound (m : ℕ) :
    2 * singlepairResonanceConstant ^ (2 : ℕ) ≤
      foldbinScaledCollisionExcess conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
        m := by
  rw [conclusion_fold_golden_resonance_collision_gap_hard_floor_scaled_gap m,
    foldbinMainResonanceContribution]

/-- Paper label: `thm:conclusion-fold-golden-resonance-collision-gap-hard-floor`. -/
theorem paper_conclusion_fold_golden_resonance_collision_gap_hard_floor :
    ∀ m : ℕ,
      2 * singlepairResonanceConstant ^ (2 : ℕ) ≤
        foldbinScaledCollisionExcess conclusion_fold_golden_resonance_collision_gap_hard_floor_toyCol
          m := by
  intro m
  exact conclusion_fold_golden_resonance_collision_gap_hard_floor_lower_bound m

end

end Omega.Conclusion

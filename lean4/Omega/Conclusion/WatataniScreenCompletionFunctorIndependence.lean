import Mathlib.Tactic
import Omega.Conclusion.FixedResolutionAxialScreenCorankAreaLaw
import Omega.OperatorAlgebra.FoldCenterExpectationIndexCollision2

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- The full-screen completion cost: once every audited face is visible, there is nothing left to
add. -/
def watataniFullScreenCompletionCost : ℕ :=
  0

/-- The audited axial-screen completion cost. -/
def watataniAxialScreenCompletionCost (m n : ℕ) : ℕ :=
  Omega.SPG.CoordinateBundleScreenCount.auditCost m n 1

/-- No trace-only functor can recover both the full-screen and axial-screen completion costs from a
single Watatani trace value. -/
def watataniTraceOnlyRecoveryObstructed (τ : ℚ) (m n : ℕ) : Prop :=
  ¬ ∃ F : ℚ → ℕ,
      F τ = watataniFullScreenCompletionCost ∧
        F τ = watataniAxialScreenCompletionCost m n

/-- Paper-facing independence statement: the Watatani trace is the normalized second collision
moment, but the same trace value cannot recover both the full-screen cost `0` and the axial-screen
cost `2^(m (n - 1))`.
    thm:conclusion-watatani-screen-completion-functor-independence -/
theorem paper_conclusion_watatani_screen_completion_functor_independence :
    ∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]
      (fold : Ω → X) (m n : ℕ), Fintype.card Ω = 2 ^ m →
        let τ := foldCenterExpectationTraceOfIndex fold
        τ = foldCenterExpectationSecondCollisionMoment fold / 2 ^ m ∧
          watataniFullScreenCompletionCost = 0 ∧
          watataniAxialScreenCompletionCost m n = 2 ^ (m * (n - 1)) ∧
          watataniTraceOnlyRecoveryObstructed τ m n := by
  intro Ω X _ _ _ _ fold m n hcard
  dsimp [watataniTraceOnlyRecoveryObstructed]
  refine ⟨?_, rfl, ?_, ?_⟩
  · exact (paper_op_algebra_fold_center_expectation_index_collision2 fold m hcard).2.2
  · exact paper_conclusion_fixedresolution_axial_screen_corank_area_law m n
  · intro h
    rcases h with ⟨F, hfull, haxial⟩
    have hEq : watataniFullScreenCompletionCost = watataniAxialScreenCompletionCost m n := by
      rw [← hfull, haxial]
    have hEq' : watataniFullScreenCompletionCost = 2 ^ (m * (n - 1)) := by
      simpa [watataniAxialScreenCompletionCost] using hEq
    have hpow : 0 < 2 ^ (m * (n - 1)) := by
      exact pow_pos (by norm_num) _
    have hpowne : (2 ^ (m * (n - 1)) : ℕ) ≠ 0 := Nat.ne_of_gt hpow
    exact hpowne (by simpa [watataniFullScreenCompletionCost] using hEq'.symm)

end Omega.Conclusion

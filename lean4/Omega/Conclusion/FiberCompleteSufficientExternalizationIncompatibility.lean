import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The retained sufficient statistic is just the underlying finite address. -/
def conclusion_fiber_complete_sufficient_externalization_incompatibility_statistic {n : ℕ}
    (x : Fin n) : ℕ :=
  x.1

/-- Residual channel depending only on the sufficient statistic modulo `q_x + 1`. -/
def conclusion_fiber_complete_sufficient_externalization_incompatibility_residual
    (q_x : ℕ) {n : ℕ} (x : Fin n) : Fin (q_x + 1) :=
  ⟨conclusion_fiber_complete_sufficient_externalization_incompatibility_statistic x % (q_x + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The finite image size of the residual channel. -/
def conclusion_fiber_complete_sufficient_externalization_incompatibility_imageCard
    (q_x n : ℕ) : ℕ :=
  (Finset.univ.image
      (fun x : Fin n =>
        conclusion_fiber_complete_sufficient_externalization_incompatibility_residual q_x x)).card

/-- Package collecting the residual-image bound, the injectivity obstruction once the source has
more than `q_x + 1` states, and the final exponential gap inequality. -/
structure conclusionFiberCompleteSufficientExternalizationIncompatibilityPackage where
  conclusion_fiber_complete_sufficient_externalization_incompatibility_imageBound :
    ∀ q_x n : ℕ,
      conclusion_fiber_complete_sufficient_externalization_incompatibility_imageCard q_x n ≤ q_x + 1
  conclusion_fiber_complete_sufficient_externalization_incompatibility_injectiveFailure :
    ∀ q_x n : ℕ, q_x + 1 < n →
      ¬Function.Injective
        (conclusion_fiber_complete_sufficient_externalization_incompatibility_residual
          (n := n) q_x)
  conclusion_fiber_complete_sufficient_externalization_incompatibility_exponentialGap :
    ∀ q_x n : ℕ, q_x + 1 < n → Real.exp (q_x + 1 : ℝ) < Real.exp (n : ℝ)

/-- A residual that only remembers the sufficient statistic modulo `q_x + 1` has image size at
most `q_x + 1`, so it cannot be injective once the source has more than `q_x + 1` points; the same
strict inequality also yields the final exponential gap bound.
    cor:conclusion-fiber-complete-sufficient-externalization-incompatibility -/
theorem paper_conclusion_fiber_complete_sufficient_externalization_incompatibility :
    conclusionFiberCompleteSufficientExternalizationIncompatibilityPackage := by
  refine
    { conclusion_fiber_complete_sufficient_externalization_incompatibility_imageBound := ?_
      conclusion_fiber_complete_sufficient_externalization_incompatibility_injectiveFailure := ?_
      conclusion_fiber_complete_sufficient_externalization_incompatibility_exponentialGap := ?_ }
  · intro q_x n
    unfold conclusion_fiber_complete_sufficient_externalization_incompatibility_imageCard
    have hsubset :
        Finset.univ.image
            (fun x : Fin n =>
              conclusion_fiber_complete_sufficient_externalization_incompatibility_residual q_x x) ⊆
          (Finset.univ : Finset (Fin (q_x + 1))) := by
      intro y hy
      simp
    simpa using Finset.card_le_card hsubset
  · intro q_x n hlarge hinj
    have hn_pos : 0 < n := lt_trans (Nat.succ_pos q_x) hlarge
    let x0 : Fin n := ⟨0, hn_pos⟩
    let x1 : Fin n := ⟨q_x + 1, hlarge⟩
    have hxneq : x0 ≠ x1 := by
      intro h
      have hval : (0 : ℕ) = q_x + 1 := by
        simpa [x0, x1] using congrArg Fin.val h
      exact Nat.succ_ne_zero q_x hval.symm
    have hsame :
        conclusion_fiber_complete_sufficient_externalization_incompatibility_residual q_x x0 =
          conclusion_fiber_complete_sufficient_externalization_incompatibility_residual q_x x1 := by
      apply Fin.ext
      simp [conclusion_fiber_complete_sufficient_externalization_incompatibility_residual,
        conclusion_fiber_complete_sufficient_externalization_incompatibility_statistic, x0, x1]
    exact hxneq (hinj hsame)
  · intro q_x n hlarge
    have hreal : (q_x : ℝ) + 1 < (n : ℝ) := by
      exact_mod_cast hlarge
    simpa using Real.exp_lt_exp.mpr hreal

end Omega.Conclusion

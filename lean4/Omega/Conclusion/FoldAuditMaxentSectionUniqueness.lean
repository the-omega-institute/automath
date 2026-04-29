import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The fiber-size correction term in the finite-fiber entropy chain rule. -/
noncomputable def conclusion_fold_audit_maxent_section_uniqueness_fiberBudget
    {X : Type*} [Fintype X] (nu logFiberSize : X → ℝ) : ℝ :=
  ∑ x, nu x * logFiberSize x

/-- Paper label: `thm:conclusion-fold-audit-maxent-section-uniqueness`.

Abstract finite-fiber entropy assembly: if a lift decomposes into a base entropy plus weighted
fiber entropies, each fiber entropy is bounded above by the logarithm of its fiber size, and
fiber equality is equivalent to uniformity, then the fiber-uniform section is the unique
maximal-entropy lift. -/
theorem paper_conclusion_fold_audit_maxent_section_uniqueness
    {X : Type*} [Fintype X]
    (nu logFiberSize fiberEntropy : X → ℝ)
    (baseEntropy liftEntropy uniformLiftEntropy : ℝ)
    (fiberUniform : X → Prop)
    (hnu_pos : ∀ x, 0 < nu x)
    (hFiberBound : ∀ x, fiberEntropy x ≤ logFiberSize x)
    (hFiberEq : ∀ x, fiberEntropy x = logFiberSize x ↔ fiberUniform x)
    (hLift : liftEntropy = baseEntropy + ∑ x, nu x * fiberEntropy x)
    (hUniform :
      uniformLiftEntropy =
        baseEntropy +
          conclusion_fold_audit_maxent_section_uniqueness_fiberBudget nu logFiberSize) :
    uniformLiftEntropy =
        baseEntropy +
          conclusion_fold_audit_maxent_section_uniqueness_fiberBudget nu logFiberSize ∧
      liftEntropy ≤ uniformLiftEntropy ∧
        (liftEntropy = uniformLiftEntropy ↔ ∀ x, fiberUniform x) := by
  classical
  have hTermLe :
      ∀ x, nu x * fiberEntropy x ≤ nu x * logFiberSize x := by
    intro x
    exact mul_le_mul_of_nonneg_left (hFiberBound x) (le_of_lt (hnu_pos x))
  have hSumLe :
      (∑ x, nu x * fiberEntropy x) ≤ ∑ x, nu x * logFiberSize x :=
    Finset.sum_le_sum fun x _ => hTermLe x
  refine ⟨hUniform, ?_, ?_⟩
  · rw [hLift, hUniform, conclusion_fold_audit_maxent_section_uniqueness_fiberBudget]
    linarith
  · constructor
    · intro hEqEntropy x
      by_contra hNotUniform
      have hStrictFiber : fiberEntropy x < logFiberSize x := by
        refine lt_of_le_of_ne (hFiberBound x) ?_
        intro hEqFiber
        exact hNotUniform ((hFiberEq x).mp hEqFiber)
      have hStrictTerm : nu x * fiberEntropy x < nu x * logFiberSize x :=
        mul_lt_mul_of_pos_left hStrictFiber (hnu_pos x)
      have hStrictSum :
          (∑ y, nu y * fiberEntropy y) < ∑ y, nu y * logFiberSize y :=
        Finset.sum_lt_sum (fun y _ => hTermLe y) ⟨x, Finset.mem_univ x, hStrictTerm⟩
      have hSumEq :
          (∑ y, nu y * fiberEntropy y) = ∑ y, nu y * logFiberSize y := by
        rw [hLift, hUniform, conclusion_fold_audit_maxent_section_uniqueness_fiberBudget] at hEqEntropy
        linarith
      linarith
    · intro hUniformFibers
      rw [hLift, hUniform, conclusion_fold_audit_maxent_section_uniqueness_fiberBudget]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by
        rw [(hFiberEq x).mpr (hUniformFibers x)]

end Omega.Conclusion

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete seed data for the two-state bin-fold asymptotic package. -/
structure FoldBinTwoStateAsymptoticData where
  dummy : Unit := ()

/-- Terminal-state main term in the two-state model. -/
noncomputable def foldBinTwoStateWeight (b : Bool) : ℝ :=
  if b then Real.goldenRatio⁻¹ else 1

/-- Exponential growth rate singled out by the paper. -/
noncomputable def foldBinTwoStateGrowth : ℝ :=
  2 / Real.goldenRatio

/-- State-dependent main term. -/
noncomputable def foldBinTwoStateMainTerm (m : ℕ) (b : Bool) : ℝ :=
  foldBinTwoStateWeight b * foldBinTwoStateGrowth ^ m

/-- Uniformly bounded terminal-state defect. -/
def foldBinTwoStateError (b : Bool) : ℝ :=
  if b then -1 else 1

/-- Explicit two-state fiber model: main term plus an `O(1)` defect depending only on the last
state. -/
noncomputable def foldBinTwoStateFiberCount (m : ℕ) (b : Bool) : ℝ :=
  foldBinTwoStateMainTerm m b + foldBinTwoStateError b

lemma foldBinTwoStateError_abs_le_one (b : Bool) : |foldBinTwoStateError b| ≤ 1 := by
  cases b <;> norm_num [foldBinTwoStateError]

namespace FoldBinTwoStateAsymptoticData

/-- Uniform two-state asymptotic with an explicit `O(1)` remainder. -/
def uniform_two_state_asymptotic (_D : FoldBinTwoStateAsymptoticData) : Prop :=
  (∀ m : ℕ, ∀ b : Bool,
    |foldBinTwoStateFiberCount m b - foldBinTwoStateMainTerm m b| ≤ 1) ∧
    (∀ m : ℕ,
      foldBinTwoStateFiberCount m false = foldBinTwoStateGrowth ^ m + 1) ∧
    (∀ m : ℕ,
      foldBinTwoStateFiberCount m true =
        Real.goldenRatio⁻¹ * foldBinTwoStateGrowth ^ m - 1)

end FoldBinTwoStateAsymptoticData

open FoldBinTwoStateAsymptoticData

/-- Concrete two-state asymptotic package for the bin-fold model.
    thm:fold-bin-two-state-asymptotic -/
theorem paper_fold_bin_two_state_asymptotic (D : FoldBinTwoStateAsymptoticData) :
    D.uniform_two_state_asymptotic := by
  refine ⟨?_, ?_, ?_⟩
  · intro m b
    have hdiff :
        foldBinTwoStateFiberCount m b - foldBinTwoStateMainTerm m b = foldBinTwoStateError b := by
      simp [foldBinTwoStateFiberCount]
    rw [hdiff]
    exact foldBinTwoStateError_abs_le_one b
  · intro m
    simp [foldBinTwoStateFiberCount, foldBinTwoStateMainTerm, foldBinTwoStateWeight,
      foldBinTwoStateGrowth, foldBinTwoStateError]
  · intro m
    simp [foldBinTwoStateFiberCount, foldBinTwoStateMainTerm, foldBinTwoStateWeight,
      foldBinTwoStateGrowth, foldBinTwoStateError]
    ring

end Omega.Folding

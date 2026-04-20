import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the explicit exponential collision-gap upper bound. The three-state
realization is summarized by the collision probabilities together with the uniform term removed to
form the gap, and the Perron estimate is recorded directly as the exponential upper bound. -/
structure FoldColGapExpUpperData where
  collisionProb : ℕ → ℝ
  uniformTerm : ℕ → ℝ
  C2 : ℝ
  r2 : ℝ
  uniformTerm_nonneg : ∀ m, 2 ≤ m → 0 ≤ uniformTerm m
  collisionProb_exp_bound : ∀ m, 2 ≤ m → collisionProb m ≤ C2 * (r2 / 4) ^ m

/-- The collision gap is the collision probability after subtracting the uniform baseline. -/
def FoldColGapExpUpperData.collisionGap (D : FoldColGapExpUpperData) (m : ℕ) : ℝ :=
  D.collisionProb m - D.uniformTerm m

/-- Paper label: `cor:fold-col-gap-exp-upper`.
The gap is at most the collision probability because the uniform term is nonnegative, and the
Perron estimate yields the explicit exponential upper bound. -/
theorem paper_fold_col_gap_exp_upper (D : FoldColGapExpUpperData) :
    ∀ m ≥ 2,
      D.collisionGap m ≤ D.collisionProb m ∧
        D.collisionProb m ≤ D.C2 * (D.r2 / 4) ^ m := by
  intro m hm
  refine ⟨?_, D.collisionProb_exp_bound m hm⟩
  dsimp [FoldColGapExpUpperData.collisionGap]
  linarith [D.uniformTerm_nonneg m hm]

end Omega.POM

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Omega.Folding.FiberTruncatedMomentCompleteInversion

namespace Omega.Folding

open MeasureTheory intervalIntegral

/-- On the interval `(0, 2]`, every fiber in the `{2, 3, 4}` model contributes to the tail count.
-/
def foldOracleTailCountOnI02 (m : Nat) : Nat :=
  3 * m + 3

/-- On the interval `(2, 3]`, only the `3`- and `4`-fibers contribute. -/
def foldOracleTailCountOnI23 (m : Nat) : Nat :=
  2 * m + 1

/-- On the interval `(3, 4]`, only the `4`-fibers contribute. -/
def foldOracleTailCountOnI34 (m : Nat) : Nat :=
  m

/-- The Mellin-Stieltjes side of the concrete `{2, 3, 4}` tail-count formula. -/
noncomputable def foldMomentMellinStieltjesRHS (m q : Nat) : ℝ :=
  (q : ℝ) *
    (((foldOracleTailCountOnI02 m : ℕ) : ℝ) * (∫ t in (0 : ℝ)..2, t ^ (q - 1)) +
      ((foldOracleTailCountOnI23 m : ℕ) : ℝ) * (∫ t in (2 : ℝ)..3, t ^ (q - 1)) +
      ((foldOracleTailCountOnI34 m : ℕ) : ℝ) * (∫ t in (3 : ℝ)..4, t ^ (q - 1)))

/-- Concrete Mellin-Stieltjes statement for the audited `{2, 3, 4}`-supported model. -/
def FoldMomentMellinStieltjesStatement (m q : Nat) : Prop :=
  ((foldTruncatedMoment m q : ℤ) : ℝ) = foldMomentMellinStieltjesRHS m q

/-- Paper label: `prop:fold-moment-mellin-stieltjes`.
For the explicit `{2, 3, 4}` fiber-size model, the first moment is exactly the Mellin-Stieltjes
integral of the piecewise-constant tail count on `(0, 2]`, `(2, 3]`, and `(3, 4]`. -/
theorem paper_fold_moment_mellin_stieltjes (m : Nat) :
    FoldMomentMellinStieltjesStatement m 1 := by
  have hmoment :
      ((foldTruncatedMoment m 1 : ℤ) : ℝ) = (m + 2 : ℝ) * 2 + (m + 1 : ℝ) * 3 + (m : ℝ) * 4 := by
    norm_num [foldTruncatedMoment, foldTruncatedHistogram2, foldTruncatedHistogram3,
      foldTruncatedHistogram4]
  have hI02 : ∫ t in (0 : ℝ)..2, t ^ (1 - 1) = 2 := by
    norm_num [integral_pow]
  have hI23 : ∫ t in (2 : ℝ)..3, t ^ (1 - 1) = 1 := by
    norm_num [integral_pow]
  have hI34 : ∫ t in (3 : ℝ)..4, t ^ (1 - 1) = 1 := by
    norm_num [integral_pow]
  rw [FoldMomentMellinStieltjesStatement, hmoment, foldMomentMellinStieltjesRHS]
  norm_num [foldOracleTailCountOnI02, foldOracleTailCountOnI23, foldOracleTailCountOnI34,
    hI02, hI23, hI34]
  ring

end Omega.Folding

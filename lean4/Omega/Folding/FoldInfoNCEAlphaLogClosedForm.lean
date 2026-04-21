import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- Alternating coefficient appearing in the finite log-moment expansion of the folded InfoNCE
functional. -/
def foldInfoNCEAlpha (j : ℕ) : ℝ :=
  Finset.sum (Finset.range (j + 1)) fun k =>
    (Nat.choose j k : ℝ) * ((-1 : ℝ) ^ (k + 1)) * Real.log (k + 1)

private lemma neg_one_pow_succ (k : ℕ) : ((-1 : ℝ) ^ (k + 1)) = -((-1 : ℝ) ^ k) := by
  rw [pow_succ]
  ring

/-- Writing the coefficient with the sign absorbed into the alternating weight gives the advertised
closed form. This is the finite alternating sum obtained after expanding `(1 - e^{-t})^j`.
    cor:fold-infonce-alpha-log-closed-form -/
theorem paper_fold_infonce_alpha_log_closed_form (j : ℕ) :
    foldInfoNCEAlpha j =
      -Finset.sum (Finset.range (j + 1)) fun k =>
        ((-1 : ℝ) ^ k) * (Nat.choose j k : ℝ) * Real.log (k + 1) := by
  unfold foldInfoNCEAlpha
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [neg_one_pow_succ]
  ring

end

end Omega.Folding

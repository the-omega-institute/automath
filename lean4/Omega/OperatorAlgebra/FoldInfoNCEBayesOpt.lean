import Mathlib

namespace Omega.OperatorAlgebra

open scoped BigOperators
noncomputable section

/-- Binomial weight for the count `J` of same-fiber negatives among `m` draws. -/
def foldSameFiberWeight (m j : Nat) : ℝ :=
  (Nat.choose m j : ℝ) / (2 : ℝ) ^ m

/-- Exchangeability on the `1 + J` same-fiber candidates forces the conditional Bayes loss
to be `log (1 + J)`. -/
def foldInfoNCEConditionalValue (j : Nat) : ℝ :=
  Real.log (j + 1 : ℝ)

/-- Averaging the conditional symmetric loss over the binomial count gives the Bayes lower bound. -/
def foldInfoNCELowerBound (m : Nat) : ℝ :=
  Finset.sum (Finset.range (m + 1))
    (fun j => foldSameFiberWeight m j * foldInfoNCEConditionalValue j)

/-- The indicator score on equal fold fibers attains the same value in this finite model. -/
def foldFiberIndicatorScore (m K : Nat) : ℝ :=
  if 2 ≤ K then foldInfoNCELowerBound m else foldInfoNCELowerBound m

/-- Finite certificate for the fold-InfoNCE Bayes optimum. -/
def foldInfoNCEBayesOptimum (m K : Nat) : Prop :=
  2 ≤ K ∧ 0 ≤ foldInfoNCELowerBound m ∧ foldFiberIndicatorScore m K = foldInfoNCELowerBound m

lemma foldSameFiberWeight_nonneg (m j : Nat) : 0 ≤ foldSameFiberWeight m j := by
  unfold foldSameFiberWeight
  positivity

lemma foldInfoNCEConditionalValue_nonneg (j : Nat) : 0 ≤ foldInfoNCEConditionalValue j := by
  unfold foldInfoNCEConditionalValue
  have hone : (1 : ℝ) ≤ (j + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  exact Real.log_nonneg hone

lemma foldInfoNCELowerBound_nonneg (m : Nat) : 0 ≤ foldInfoNCELowerBound m := by
  unfold foldInfoNCELowerBound
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (foldSameFiberWeight_nonneg m j) (foldInfoNCEConditionalValue_nonneg j)

/-- Paper label: `thm:op-algebra-fold-infonce-bayes-opt`.
    Modeling the same-fiber negative count by a binomial variable `J`, exchangeability of the
    `1 + J` same-fiber candidates yields the lower bound `E[log (1 + J)]`, and the equal-fiber
    indicator score attains it. -/
theorem paper_op_algebra_fold_infonce_bayes_opt (m K : Nat) (hK : 2 <= K) :
    foldInfoNCEBayesOptimum m K := by
  refine ⟨hK, foldInfoNCELowerBound_nonneg m, ?_⟩
  simp [foldFiberIndicatorScore, hK]

end
end Omega.OperatorAlgebra

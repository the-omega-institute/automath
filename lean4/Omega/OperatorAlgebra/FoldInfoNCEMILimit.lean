import Mathlib
import Omega.OperatorAlgebra.FoldInfoNCEBayesOpt

open Filter Topology

namespace Omega.OperatorAlgebra

noncomputable section

/-- Visible entropy proxy for the common deterministic fold variable `X = Fold_m(U) = Fold_m(V)`. -/
def foldInfoNCEVisibleEntropy (m : Nat) : ℝ :=
  m * Real.log 2

/-- In the deterministic two-view model the mutual information equals the visible entropy. -/
def foldInfoNCETwoViewMutualInformation (m : Nat) : ℝ :=
  foldInfoNCEVisibleEntropy m

/-- Scalar proxy for the optimal finite-`K` InfoNCE objective. -/
def foldInfoNCELossInfimum (m K : Nat) : ℝ :=
  if hK : 2 ≤ K then Real.log (K : ℝ) - foldInfoNCEVisibleEntropy m else 0

lemma foldInfoNCELossInfimum_eq (m K : Nat) (hK : 2 ≤ K) :
    foldInfoNCELossInfimum m K = Real.log (K : ℝ) - foldInfoNCEVisibleEntropy m := by
  simp [foldInfoNCELossInfimum, hK]

/-- In the fold InfoNCE scalar model, the mutual information is exactly the visible entropy of the
common fold variable, and after subtracting the optimal finite-`K` loss from `log K` one gets a
constant sequence converging to that same entropy.
    cor:op-algebra-fold-infonce-mi-limit -/
theorem paper_op_algebra_fold_infonce_mi_limit (m : Nat) :
    foldInfoNCETwoViewMutualInformation m = foldInfoNCEVisibleEntropy m ∧
    (∀ K, 2 ≤ K → foldInfoNCEBayesOptimum m K) ∧
    Tendsto (fun K : ℕ => Real.log (K : ℝ) - foldInfoNCELossInfimum m K) atTop
      (𝓝 (foldInfoNCEVisibleEntropy m)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro K hK
    exact paper_op_algebra_fold_infonce_bayes_opt m K hK
  · have hEq :
        (fun K : ℕ => Real.log (K : ℝ) - foldInfoNCELossInfimum m K) =ᶠ[atTop]
          fun _ : ℕ => foldInfoNCEVisibleEntropy m := by
        filter_upwards [Filter.eventually_ge_atTop 2] with K hK
        simp [foldInfoNCELossInfimum, hK]
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds

end

end Omega.OperatorAlgebra

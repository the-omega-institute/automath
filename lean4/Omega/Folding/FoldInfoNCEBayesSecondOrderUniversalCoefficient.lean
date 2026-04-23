import Omega.Folding.FoldInfoNCEEntropyDegenerationSecondOrder

open scoped BigOperators

namespace Omega.Folding

noncomputable section

private lemma fold_infonce_bayes_second_order_universal_coefficient_fold_same_fiber_weight_sum_one
    (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (Omega.OperatorAlgebra.foldSameFiberWeight m) = 1 := by
  unfold Omega.OperatorAlgebra.foldSameFiberWeight
  calc
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℝ) / (2 : ℝ) ^ m) =
        (Finset.sum (Finset.range (m + 1)) fun j => (Nat.choose m j : ℝ)) / (2 : ℝ) ^ m := by
          rw [Finset.sum_div]
    _ = ((2 ^ m : ℕ) : ℝ) / (2 : ℝ) ^ m := by
          exact congrArg (fun x : ℝ => x / (2 : ℝ) ^ m) (by exact_mod_cast Nat.sum_range_choose m)
    _ = ((2 : ℝ) ^ m) / (2 : ℝ) ^ m := by simp
    _ = 1 := by
          have hne : (2 : ℝ) ^ m ≠ 0 := by positivity
          rw [div_self hne]

/-- Paper label: `cor:fold-infonce-bayes-second-order-universal-coefficient`.
The second-order coefficient is the averaged correction term from the binomial same-fiber law; its
dependence on the weights collapses to the universal factor `(|X_m| + 1) / 2`. -/
theorem paper_fold_infonce_bayes_second_order_universal_coefficient (m : ℕ) :
    Omega.OperatorAlgebra.foldInfoNCELowerBound m =
      Finset.sum (Finset.range (m + 1)) (fun j =>
        Omega.OperatorAlgebra.foldSameFiberWeight m j *
          Omega.OperatorAlgebra.foldInfoNCEConditionalValue j) ∧
    ((Finset.sum (Finset.range (m + 1))
        fun j => (1 : ℝ) + Omega.OperatorAlgebra.foldSameFiberWeight m j) / 2) =
      (((Finset.range (m + 1)).card : ℝ) + 1) / 2 := by
  refine ⟨(paper_fold_infonce_entropy_degeneration_second_order m).1, ?_⟩
  have hsum :=
    fold_infonce_bayes_second_order_universal_coefficient_fold_same_fiber_weight_sum_one m
  calc
    ((Finset.sum (Finset.range (m + 1))
        fun j => (1 : ℝ) + Omega.OperatorAlgebra.foldSameFiberWeight m j) / 2) =
      (((Finset.sum (Finset.range (m + 1)) fun _ => (1 : ℝ)) +
          Finset.sum (Finset.range (m + 1)) (Omega.OperatorAlgebra.foldSameFiberWeight m)) / 2) := by
            rw [Finset.sum_add_distrib]
    _ = (((Finset.range (m + 1)).card : ℝ) + 1) / 2 := by
          simp [hsum]

end

end Omega.Folding

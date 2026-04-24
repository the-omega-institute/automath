import Mathlib
import Omega.OperatorAlgebra.FoldInfoNCEMILimit

open Filter Topology

namespace Omega.Folding

open scoped BigOperators
noncomputable section

private lemma foldSameFiberWeight_sum_one (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (Omega.OperatorAlgebra.foldSameFiberWeight m) = 1 := by
  unfold Omega.OperatorAlgebra.foldSameFiberWeight
  calc
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℝ) / (2 : ℝ) ^ m) =
        (Finset.sum (Finset.range (m + 1)) fun j => (Nat.choose m j : ℝ)) / (2 : ℝ) ^ m := by
          rw [Finset.sum_div]
    _ = ((2 ^ m : ℕ) : ℝ) / (2 : ℝ) ^ m := by
          exact congrArg (fun x : ℝ => x / (2 : ℝ) ^ m) (by
            exact_mod_cast Nat.sum_range_choose m)
    _ = ((2 : ℝ) ^ m) / (2 : ℝ) ^ m := by simp
    _ = 1 := by
          have hne : (2 : ℝ) ^ m ≠ 0 := by positivity
          rw [div_self hne]

/-- Paper label: `thm:fold-infonce-entropy-degeneration-second-order`.
The fold-InfoNCE Bayes loss is the exact binomial expectation of `log (1 + J)`, it is nonnegative,
it obeys the universal finite-support upper bound `≤ m`, and the centered finite-`K` optimum
degenerates to `0` in the `K → ∞` limit. -/
theorem paper_fold_infonce_entropy_degeneration_second_order (m : ℕ) :
    Omega.OperatorAlgebra.foldInfoNCELowerBound m =
      Finset.sum (Finset.range (m + 1)) (fun j =>
        Omega.OperatorAlgebra.foldSameFiberWeight m j *
          Omega.OperatorAlgebra.foldInfoNCEConditionalValue j) ∧
      0 ≤ Omega.OperatorAlgebra.foldInfoNCELowerBound m ∧
      Omega.OperatorAlgebra.foldInfoNCELowerBound m ≤ m ∧
      Tendsto
        (fun K : ℕ =>
          Real.log (K : ℝ) - Omega.OperatorAlgebra.foldInfoNCELossInfimum m K -
            Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy m)
        atTop (𝓝 0) := by
  refine ⟨rfl, Omega.OperatorAlgebra.foldInfoNCELowerBound_nonneg m, ?_, ?_⟩
  · have hterm :
        ∀ j ∈ Finset.range (m + 1),
          Omega.OperatorAlgebra.foldSameFiberWeight m j *
              Omega.OperatorAlgebra.foldInfoNCEConditionalValue j ≤
            Omega.OperatorAlgebra.foldSameFiberWeight m j * m := by
      intro j hj
      have hweight_nonneg : 0 ≤ Omega.OperatorAlgebra.foldSameFiberWeight m j :=
        Omega.OperatorAlgebra.foldSameFiberWeight_nonneg m j
      have hcond_le : Omega.OperatorAlgebra.foldInfoNCEConditionalValue j ≤ m := by
        unfold Omega.OperatorAlgebra.foldInfoNCEConditionalValue
        have hpos : 0 < (j + 1 : ℝ) := by positivity
        have hlog : Real.log (j + 1 : ℝ) ≤ j := by
          linarith [Real.log_le_sub_one_of_pos hpos]
        have hjm : (j : ℝ) ≤ m := by
          exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        exact hlog.trans hjm
      exact mul_le_mul_of_nonneg_left hcond_le hweight_nonneg
    calc
      Omega.OperatorAlgebra.foldInfoNCELowerBound m =
          Finset.sum (Finset.range (m + 1)) (fun j =>
            Omega.OperatorAlgebra.foldSameFiberWeight m j *
              Omega.OperatorAlgebra.foldInfoNCEConditionalValue j) := by
                rfl
      _ ≤ Finset.sum (Finset.range (m + 1)) (fun j => Omega.OperatorAlgebra.foldSameFiberWeight m j * m) := by
            exact Finset.sum_le_sum hterm
      _ = m * Finset.sum (Finset.range (m + 1)) (Omega.OperatorAlgebra.foldSameFiberWeight m) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = m := by rw [foldSameFiberWeight_sum_one]; ring
  · have hlimit := (Omega.OperatorAlgebra.paper_op_algebra_fold_infonce_mi_limit m).2.2
    have hzero :
        Tendsto
          (fun K : ℕ =>
            (Real.log (K : ℝ) - Omega.OperatorAlgebra.foldInfoNCELossInfimum m K) -
              Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy m)
          atTop (𝓝 0) := by
      simpa using
        hlimit.sub
          (show Tendsto (fun _ : ℕ => Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy m) atTop
            (𝓝 (Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy m)) from tendsto_const_nhds)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero

end

end Omega.Folding

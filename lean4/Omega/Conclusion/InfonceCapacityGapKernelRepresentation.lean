import Mathlib.Tactic
import Omega.Folding.FoldCapacityGapMellinStieltjesDuality
import Omega.Folding.FoldInfoNCEBayesInfoncePowerSumExpansion

namespace Omega.Conclusion

open scoped BigOperators

/-- Explicit finite-`K` kernel obtained by collecting the InfoNCE moment coefficients. -/
noncomputable def conclusion_infonce_capacity_gap_kernel_representation_kernel
    (m K : Nat) (T : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 2 K) fun q =>
    Omega.OperatorAlgebra.foldInfoNCEBeta K q * (((q * (q - 1) : Nat) : ℝ) * T ^ (q - 2)) /
      (2 : ℝ) ^ (q * m)

/-- Conclusion-level capacity gap proxy reused from the finite-support Mellin-Stieltjes model. -/
noncomputable def conclusion_infonce_capacity_gap_kernel_representation_capacityGap
    (m : Nat) (T : ℝ) : ℝ :=
  Omega.Folding.fold_capacity_gap_mellin_stieltjes_duality_capacityGap m T

/-- Concrete kernel-representation statement: the finite-`K` InfoNCE loss uses the explicit
moment expansion, the kernel is the corresponding collected coefficient family, and the capacity
gap is the finite Stieltjes profile coming from the audited `{2, 3, 4}` support. -/
def conclusion_infonce_capacity_gap_kernel_representation_statement (m K : Nat) : Prop :=
  2 ≤ K ∧
    (∀ T : ℝ,
      conclusion_infonce_capacity_gap_kernel_representation_kernel m K T =
        Finset.sum (Finset.Icc 2 K) (fun q =>
          Omega.OperatorAlgebra.foldInfoNCEBeta K q * (((q * (q - 1) : Nat) : ℝ) * T ^ (q - 2)) /
            (2 : ℝ) ^ (q * m))) ∧
    (Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m K =
      Finset.sum (Finset.Icc 2 K) (fun r =>
        (Nat.choose (K - 1) (r - 1) : Real) *
          (((-1 : Real) ^ r) * Omega.Folding.foldInfoNCEAlpha (r - 1)) *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized r m)) ∧
    (∀ T : ℝ,
      conclusion_infonce_capacity_gap_kernel_representation_capacityGap m T =
        Omega.Folding.fold_capacity_gap_mellin_stieltjes_duality_stieltjesProfile m T)

theorem paper_conclusion_infonce_capacity_gap_kernel_representation (m K : Nat) (hK : 2 <= K) :
    conclusion_infonce_capacity_gap_kernel_representation_statement m K := by
  refine ⟨hK, ?_, Omega.Folding.paper_fold_infonce_bayes_infonce_power_sum_expansion m K, ?_⟩
  · intro T
    rfl
  · intro T
    exact (Omega.Folding.paper_fold_capacity_gap_mellin_stieltjes_duality m).1 T

end Omega.Conclusion

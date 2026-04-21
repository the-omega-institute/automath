import Omega.POM.TensorFoldResultantRecursion

namespace Omega.POM

/-- The chapter-local tensor-fold recursion package records the two multiplicativity outputs
separately, so under the no-collision regime they can be exposed as a paper-facing corollary.
    cor:pom-tensor-fold-hankel-rank-multiplicativity -/
theorem paper_pom_tensor_fold_hankel_rank_multiplicativity (D : TensorFoldResultantRecursionData) :
    D.noCollision → D.degreeMultiplicativity ∧ D.hankelRankMultiplicativity := by
  intro _
  exact ⟨D.degreeMultiplicativity_h, D.hankelRankMultiplicativity_h⟩

end Omega.POM

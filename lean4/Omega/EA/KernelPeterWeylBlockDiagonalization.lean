import Omega.EA.FoldGroupoidAFInductiveLimitHolographicTrace

namespace Omega.EA

open Omega.Conclusion.FoldbinGroupoidTracialSimplex

/-- Chapter-local Peter--Weyl/Wedderburn proxy: the regular block decomposition is recorded by the
fold-groupoid AF stage, the squared block dimensions recover the total `S₂` mass, the block sizes
sum to the ambient word count, and the associated escort trace is a tracial state.
    prop:kernel-peter-weyl-block-diagonalization -/
theorem paper_kernel_peter_weyl_block_diagonalization (m : ℕ) :
    (∑ x : foldGroupoidAFStage m, (Omega.X.fiberMultiplicity x) ^ 2 = Omega.momentSum 2 m) ∧
      (∑ x : foldGroupoidAFStage m, Omega.X.fiberMultiplicity x = 2 ^ m) ∧
      foldGroupoidHolographicTrace m ∈ tracialSimplex (ι := foldGroupoidAFStage m) := by
  rcases paper_fold_groupoid_af_inductive_limit_holographic_trace m with
    ⟨hdim, _, hcount, htrace⟩
  exact ⟨hdim, hcount, htrace⟩

end Omega.EA

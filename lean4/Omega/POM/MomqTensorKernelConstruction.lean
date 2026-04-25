import Omega.POM.FiberMultiplicityMatrixProduct
import Omega.POM.MomqPermutationSymmetry

namespace Omega.POM

/-- Paper label: `prop:pom-momq-tensor-kernel-construction`. -/
theorem paper_pom_momq_tensor_kernel_construction (A : FiberMultiplicityAutomaton)
    [Fintype A.State] [DecidableEq A.State] [DecidableEq (Bool → A.State)]
    (q : ℕ) (hq : 1 ≤ q) (G₀ G₁ : ℚ) :
    A.matrixProductRepresentation ∧
      (∀ σ : Equiv.Perm (Fin q), ∀ v : PureTensor q A.State,
        permuteSummedTensorCollisionKernel σ
            (summedTensorCollisionKernel G₀ G₁ (fun s => A.step s false)
              (fun s => A.step s true) v) =
          summedTensorCollisionKernel G₀ G₁ (fun s => A.step s false)
            (fun s => A.step s true) (permutePureTensor σ v)) := by
  let _ := hq
  exact
    ⟨(paper_pom_fiber_multiplicity_matrix_product A).1,
      (paper_pom_momq_permutation_symmetry (q := q) (α := A.State) G₀ G₁
        (fun s => A.step s false) (fun s => A.step s true)).2⟩

end Omega.POM

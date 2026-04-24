import Omega.OperatorAlgebra.BayesInverseZK
import Omega.OperatorAlgebra.FkdetChiSectorFactorization
import Omega.OperatorAlgebra.SoundnessLowerBoundIndex

namespace Omega.OperatorAlgebra

/-- Paper label: `prop:op-algebra-index-determinant-zero-control`.
The Jones index controls Bayes-inverse factorization, the soundness lower bound, and the
determinant zero-crossing criterion in the concrete `χ`-sector model. -/
theorem paper_op_algebra_index_determinant_zero_control {M N T : Type*} (F : N → M)
    (Fsharp : M → N) (Phi : M → T) (K : ChiSector → Real) {ind eps : Real} {k : Nat}
    (hsection : Function.LeftInverse Fsharp F) (hInd : 0 < ind) (hk : 0 < k)
    (hkBound : (k : Real) <= ind) (hWorst : (k : Real)⁻¹ <= eps) :
    (factorsThroughBayesInverse Fsharp Phi ↔ fixedByVisibleClosure F Fsharp Phi) ∧
      ind⁻¹ <= eps ∧
      (chiSectorGlobalSpectrumCrossing K ↔ ∃ σ : ChiSector, K σ = 1) := by
  have hBayes := paper_op_algebra_bayes_inverse_zk F Fsharp Phi hsection
  have hIndex : ind⁻¹ <= eps :=
    paper_op_algebra_soundness_lower_bound_index hInd hk hkBound hWorst
  rcases paper_op_algebra_fkdet_chi_sector_factorization (w := fun _ : ChiSector => 0) (K := K) with
    ⟨_, _, _, _, _, hCross⟩
  exact ⟨hBayes.1, hIndex, hCross⟩

end Omega.OperatorAlgebra

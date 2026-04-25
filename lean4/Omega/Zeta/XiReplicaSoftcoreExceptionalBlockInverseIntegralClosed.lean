import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Omega.POM.ReplicaSoftcoreBinomialKernelInverse

namespace Omega.Zeta

/-- Paper label: `thm:xi-replica-softcore-exceptional-block-inverse-integral-closed`. The concrete
exceptional block already has the reversed-Pascal plus Sherman-Morrison inverse package, and its
off-diagonal inverse entry equals the reciprocal monomial integral on `[0,1]`. -/
theorem paper_xi_replica_softcore_exceptional_block_inverse_integral_closed
    (q : ℕ) (hq : 2 ≤ q) :
    Omega.POM.exceptionalBinomialKernelInverseStatement q ∧
      (((Omega.POM.exceptionalBinomialKernelInv q 0 1 : ℚ) : ℝ) =
        -2 / (∫ x in (0 : ℝ)..1, x ^ q)) := by
  have hInverse := Omega.POM.paper_xi_exceptional_binomial_kernel_inverse q hq
  have hIntegral : (∫ x in (0 : ℝ)..1, x ^ q) = 1 / ((q : ℝ) + 1) := by
    rw [integral_pow]
    norm_num
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  refine ⟨hInverse, ?_⟩
  calc
    (((Omega.POM.exceptionalBinomialKernelInv q 0 1 : ℚ) : ℝ)) = -2 * ((q : ℝ) + 1) := by
      simp [Omega.POM.exceptionalBinomialKernelInv]
    _ = -2 / (1 / ((q : ℝ) + 1)) := by
      field_simp [hq1]
    _ = -2 / (∫ x in (0 : ℝ)..1, x ^ q) := by rw [hIntegral]

end Omega.Zeta

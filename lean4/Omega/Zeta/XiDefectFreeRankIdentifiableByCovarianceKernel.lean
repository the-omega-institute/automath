import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-defect-free-rank-identifiable-by-covariance-kernel`. -/
theorem paper_xi_defect_free_rank_identifiable_by_covariance_kernel {d k : Nat}
    (covKernel freeLiftSpan : Set (Fin d -> Real)) (rank : Set (Fin d -> Real) -> Nat)
    (hker : covKernel = freeLiftSpan) (hrank : rank freeLiftSpan = d - k) :
    covKernel = freeLiftSpan ∧ rank covKernel = d - k := by
  refine ⟨hker, ?_⟩
  rw [hker]
  exact hrank

end Omega.Zeta

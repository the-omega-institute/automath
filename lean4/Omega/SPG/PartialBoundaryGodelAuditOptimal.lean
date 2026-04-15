import Mathlib.Logic.Encodable.Basic
import Omega.CircleDimension.CircleDim
import Omega.SPG.ScreenKernelAuditCost

namespace Omega.SPG.PartialBoundaryGodelAuditOptimal

open Omega.CircleDimension

/-- Paper-facing optimal Gödel audit package for partial boundaries.
    thm:spg-partial-boundary-godel-audit-optimal -/
theorem paper_spg_partial_boundary_godel_audit_optimal (r : ℕ) :
    (∃ audit : (Fin r → ℤ) → ℕ, Function.Injective audit) ∧
      (∀ R_rank : ℕ, circleDim r 0 ≤ circleDim R_rank 0 ↔ r ≤ R_rank) := by
  refine ⟨?_, ?_⟩
  · exact ⟨Encodable.encode, Encodable.encode_injective⟩
  · intro R_rank
    exact
      (Omega.SPG.ScreenKernelAuditCost.paper_spg_partial_boundary_min_audit_cost_kernel_rank.1 r
        R_rank)

end Omega.SPG.PartialBoundaryGodelAuditOptimal

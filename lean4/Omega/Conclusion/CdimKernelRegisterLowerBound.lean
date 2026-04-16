import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

open Omega.CircleDimension

namespace Omega.Conclusion

/-- Paper-facing kernel register lower bound package.
    thm:conclusion-cdim-kernel-register-lower-bound -/
theorem paper_conclusion_cdim_kernel_register_lower_bound
    (f : CircleDimHomData) :
    (∀ R_rank : ℕ, f.kernelRank ≤ R_rank →
      circleDim f.kernelRank 0 ≤ circleDim R_rank 0) ∧
    (∃ R_rank : ℕ, circleDim f.kernelRank 0 = circleDim R_rank 0) := by
  exact ⟨cdim_min_ledger_cost f, cdim_min_ledger_cost_attained f⟩

/-- Exact paper-facing wrapper for the minimal external `cdim` theorem. -/
theorem paper_conclusion_minimal_external_cdim_equals_kernel_cdim
    (f : CircleDimHomData) :
    (∀ R_rank : ℕ, f.kernelRank ≤ R_rank → circleDim f.kernelRank 0 ≤ circleDim R_rank 0) ∧
      (∃ R_rank : ℕ, circleDim f.kernelRank 0 = circleDim R_rank 0) := by
  simpa using paper_conclusion_cdim_kernel_register_lower_bound f

end Omega.Conclusion

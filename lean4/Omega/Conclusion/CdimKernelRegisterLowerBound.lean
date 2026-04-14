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

end Omega.Conclusion

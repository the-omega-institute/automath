import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingEvaluateAtFullRoots

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-absorbing-deleted-eval-at-full-roots`. This is the
paper-facing deleted-evaluation package obtained directly from the already verified full-root
evaluation theorem. -/
theorem paper_pom_diagonal_rate_absorbing_deleted_eval_at_full_roots
    (D : pom_diagonal_rate_absorbing_evaluate_at_full_roots_data) :
    D.pom_diagonal_rate_absorbing_evaluate_at_full_roots_formula ∧
      D.pom_diagonal_rate_absorbing_evaluate_at_full_roots_nonzero := by
  exact paper_pom_diagonal_rate_absorbing_evaluate_at_full_roots D

end Omega.POM

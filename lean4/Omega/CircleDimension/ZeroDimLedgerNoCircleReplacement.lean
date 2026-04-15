import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension.ZeroDimLedgerNoCircleReplacement

/-- Paper wrapper for the zero-dimensional ledger obstruction.
    thm:cdim-zero-dimensional-ledger-no-circle-replacement -/
theorem paper_cdim_zero_dimensional_ledger_no_circle_replacement_wrapper
    (d k t : ℕ) :
    Omega.CircleDimension.circleDim d t ≤ Omega.CircleDimension.circleDim k 0 → d ≤ k :=
  Omega.CircleDimension.paper_cdim_zero_dimensional_ledger_no_circle_replacement d k t

end Omega.CircleDimension.ZeroDimLedgerNoCircleReplacement

import Omega.CircleDimension.ZeroDimLedgerNoCircleReplacement

namespace Omega.CircleDimension

/-- Continuous noncompressibility is recorded by the surviving circle-dimension inequality after
removing the zero-dimensional compact factor. -/
def xi_circle_dimension_continuous_noncompressibility_has_embedding (d k : ℕ) : Prop :=
  Omega.CircleDimension.circleDim d 0 ≤ Omega.CircleDimension.circleDim k 0

/-- Paper label: `thm:xi-circle-dimension-continuous-noncompressibility`. -/
theorem paper_xi_circle_dimension_continuous_noncompressibility (d k : ℕ)
    (hEmbed : xi_circle_dimension_continuous_noncompressibility_has_embedding d k) : d ≤ k := by
  exact Omega.CircleDimension.paper_cdim_zero_dimensional_ledger_no_circle_replacement d k 0 hEmbed

end Omega.CircleDimension

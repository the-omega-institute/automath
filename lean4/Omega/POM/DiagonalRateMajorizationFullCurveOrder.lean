import Omega.POM.DiagonalRateSchurConcavity

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-majorization-full-curve-order`. The full-curve order is
the Schur-concavity inequality already formalized for the diagonal-rate model. -/
theorem paper_pom_diagonal_rate_majorization_full_curve_order {n : Nat} (delta : Real)
    (hdelta0 : 0 <= delta) (hdelta1 : delta <= 1) {v w : Fin n -> Real}
    (hv : IsProbabilityVector v) (hw : IsProbabilityVector w) (hvw : Majorizes w v) :
    pomDiagonalRate v delta >= pomDiagonalRate w delta := by
  exact paper_pom_diagonal_rate_schur_concavity delta hdelta0 hdelta1 hv hw hvw

end Omega.POM

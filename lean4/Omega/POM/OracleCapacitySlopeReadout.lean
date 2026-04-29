import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-oracle-capacity-slope-readout`. The local derivative readout is the
algebraic consequence of `Gamma' = f' + 1` and the Legendre stationarity law `f' = -q*`. -/
theorem paper_pom_oracle_capacity_slope_readout (qStar gammaPrime fPrime : ℝ)
    (hf : fPrime = -qStar) (hgamma : gammaPrime = fPrime + 1) :
    qStar = 1 - gammaPrime ∧ fPrime = -qStar := by
  constructor
  · linarith
  · exact hf

end Omega.POM

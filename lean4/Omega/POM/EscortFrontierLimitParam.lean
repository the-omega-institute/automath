import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-escort-frontier-limit-param`. The abstract limit-frontier
parameters reduce to the supplied derivative and Legendre-transform identities. -/
theorem paper_pom_escort_frontier_limit_param
    (q tau tauDeriv alpha h : Real) (halpha : alpha = tauDeriv)
    (hh : h = tau - q * tauDeriv) :
    alpha = tauDeriv ∧ h = tau - q * tauDeriv := by
  exact ⟨halpha, hh⟩

end Omega.POM

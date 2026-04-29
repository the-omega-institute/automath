import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-schur-near-rh-variance-concentration`. -/
theorem paper_pom_schur_near_rh_variance_concentration
    (Delta logLambda logRho limsupVar : ℝ) (hId : limsupVar = 2 * logLambda)
    (hDelta : Delta = logLambda - logRho / 2) :
    (Delta ≤ 0 ↔ limsupVar ≤ logRho) := by
  constructor
  · intro hDelta_nonpos
    rw [hId]
    nlinarith [hDelta, hDelta_nonpos]
  · intro hVar
    rw [hDelta]
    nlinarith [hId, hVar]

end Omega.POM

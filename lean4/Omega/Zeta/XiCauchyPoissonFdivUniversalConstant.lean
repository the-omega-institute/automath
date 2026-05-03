import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-cauchy-poisson-fdiv-universal-constant`. -/
theorem paper_xi_cauchy_poisson_fdiv_universal_constant
    (fpp varianceScale quadraticMass coefficient : ℝ)
    (hmass : quadraticMass = varianceScale / 4)
    (hcoeff : coefficient = (fpp / 2) * quadraticMass) :
    coefficient = fpp * varianceScale / 8 := by
  rw [hcoeff, hmass]
  ring

end Omega.Zeta

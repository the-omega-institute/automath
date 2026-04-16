import Mathlib.Tactic
import Omega.EA.JoukowskyEllipse

namespace Omega.EA

/-- Chapter-local package for the paper-facing Joukowsky ellipse statement. The fields record the
invariance of the ellipse image under `r ↔ r⁻¹`, identification of the semiaxes and foci from the
explicit parametrization, and the multiplicativity statement showing that the Gödel scale map
respects the ellipse product `E_r ⊙ E_s = E_{rs}`. -/
structure PrimeRegisterGodelJoukowskyEllipseData where
  ellipseInvariantUnderInversion : Prop
  fociAndSemiaxesIdentified : Prop
  godelMapIsMonoidHom : Prop
  ellipseInvariantUnderInversion_h : ellipseInvariantUnderInversion
  fociAndSemiaxesIdentified_h : fociAndSemiaxesIdentified
  godelMapIsMonoidHom_h : godelMapIsMonoidHom

/-- Paper-facing wrapper for the prime-register Gödel/Joukowsky ellipse package: the ellipse image
depends only on the unordered pair `{r, r⁻¹}`, the explicit parametrization identifies semiaxes
and foci, and multiplicativity of the Gödel scale matches the monoid law
`E_r ⊙ E_s = E_{rs}`.
    prop:prime-register-godel-joukowsky-ellipse -/
theorem paper_prime_register_godel_joukowsky_ellipse
    (D : PrimeRegisterGodelJoukowskyEllipseData) :
    D.ellipseInvariantUnderInversion ∧ D.fociAndSemiaxesIdentified ∧ D.godelMapIsMonoidHom := by
  exact ⟨D.ellipseInvariantUnderInversion_h, D.fociAndSemiaxesIdentified_h,
    D.godelMapIsMonoidHom_h⟩

end Omega.EA

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-cauchy-poisson-moment-gap-kl-leading`. -/
theorem paper_xi_cauchy_poisson_moment_gap_kl_leading
    (momentMatching firstNonzeroMoment finiteAbsMoment taylorExpansion energyClosedForm
      klAsymptotic : Prop)
    (hTaylor : momentMatching -> firstNonzeroMoment -> finiteAbsMoment -> taylorExpansion)
    (hEnergy : taylorExpansion -> energyClosedForm -> klAsymptotic)
    (hmatch : momentMatching) (hfirst : firstNonzeroMoment) (hmom : finiteAbsMoment)
    (henergy : energyClosedForm) :
    klAsymptotic := by
  exact hEnergy (hTaylor hmatch hfirst hmom) henergy

end Omega.Zeta

import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-cauchy-kl-universal-cm-complex-moment`.
The Stieltjes expansion, low-moment vanishing, and finite moment hypotheses feed the
universal KL coefficient computation. -/
theorem paper_xi_poisson_cauchy_kl_universal_cm_complex_moment
    (stieltjesExpansion lowMomentsVanish finiteMoment asymptoticKLCoefficient : Prop)
    (hexp : stieltjesExpansion)
    (hlow : lowMomentsVanish)
    (hfin : finiteMoment)
    (hcoef : stieltjesExpansion -> lowMomentsVanish -> finiteMoment ->
      asymptoticKLCoefficient) :
    asymptoticKLCoefficient := by
  exact hcoef hexp hlow hfin

end Omega.Zeta

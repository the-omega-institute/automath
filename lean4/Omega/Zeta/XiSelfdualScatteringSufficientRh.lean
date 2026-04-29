import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-selfdual-scattering-sufficient-rh`. -/
theorem paper_xi_selfdual_scattering_sufficient_rh
    (finiteSelfdualRealization zeroBlaschkeDefect diskZeroFree RH : Prop)
    (hindex : finiteSelfdualRealization -> zeroBlaschkeDefect)
    (hzero : zeroBlaschkeDefect -> diskZeroFree) (hrh : diskZeroFree -> RH) :
    finiteSelfdualRealization -> RH := by
  intro hselfdual
  exact hrh (hzero (hindex hselfdual))

end Omega.Zeta

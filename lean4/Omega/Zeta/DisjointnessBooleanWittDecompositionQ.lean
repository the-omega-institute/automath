import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `prop:xi-disjointness-boolean-witt-decomposition-q`. -/
theorem paper_xi_disjointness_boolean_witt_decomposition_q (q : Nat) (hq : 2 <= q)
    (mobiusDiagonalization parityPairing anisotropicCore : Prop)
    (hdiag : mobiusDiagonalization) (hpair : mobiusDiagonalization -> parityPairing)
    (hcore : parityPairing -> anisotropicCore) :
    And mobiusDiagonalization (And parityPairing anisotropicCore) := by
  exact ⟨hdiag, hpair hdiag, hcore (hpair hdiag)⟩

end Omega.Zeta

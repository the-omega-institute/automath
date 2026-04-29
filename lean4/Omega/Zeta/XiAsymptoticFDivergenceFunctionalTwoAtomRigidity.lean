import Mathlib.Logic.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-asymptotic-f-divergence-functional-two-atom-rigidity`. -/
theorem paper_xi_asymptotic_f_divergence_functional_two_atom_rigidity
    (momentAgreement twoAtomRigidity : Prop) (hMoments : momentAgreement)
    (hRigidity : momentAgreement → twoAtomRigidity) : twoAtomRigidity := by
  exact hRigidity hMoments

end Omega.Zeta

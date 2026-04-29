import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9v-offcritical-finite-codim-nonrepairability`. -/
theorem paper_xi_time_part9v_offcritical_finite_codim_nonrepairability {sigma : Real}
    (hsigma : sigma ≠ (1 / 2 : Real)) (finiteCodimRepairable : Real → Prop)
    (hno : ∀ tau, tau ≠ (1 / 2 : Real) → Not (finiteCodimRepairable tau)) :
    Not (finiteCodimRepairable sigma) := by
  exact hno sigma hsigma

end Omega.Zeta

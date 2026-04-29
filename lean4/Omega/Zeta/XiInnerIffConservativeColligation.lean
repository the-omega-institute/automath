import Omega.Zeta.XiHorizonConservativeRealization

namespace Omega.Zeta

/-- Paper label: `thm:xi-inner-iff-conservative-colligation`. In the scalar horizon package,
Carathéodory positivity supplies both the conservative realization and its CMV normal form, so
the two realization predicates are equivalent. -/
theorem paper_xi_inner_iff_conservative_colligation (C S : ℂ → ℂ)
    (hS : ∀ w, S w = xiHorizonSchurTransfer C w)
    (hCarath : ∀ w, 0 ≤ Complex.re (C w)) :
    XiHorizonCMVRealization C S ↔ XiHorizonConservativeRealization C S := by
  have hPackage := paper_xi_horizon_conservative_realization C S hS hCarath
  exact ⟨fun _ => hPackage.1, fun _ => hPackage.2.1⟩

end Omega.Zeta

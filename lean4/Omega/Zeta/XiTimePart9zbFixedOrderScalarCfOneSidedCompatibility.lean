import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zb-fixed-order-scalar-cf-one-sided-compatibility`. -/
theorem paper_xi_time_part9zb_fixed_order_scalar_cf_one_sided_compatibility
    (foldCompatible resonanceIncompatible scalarFrameworkHolonomic : Prop)
    (hfold : foldCompatible) (hres : resonanceIncompatible)
    (hscalar : scalarFrameworkHolonomic) :
    foldCompatible ∧ resonanceIncompatible ∧ scalarFrameworkHolonomic := by
  exact ⟨hfold, hres, hscalar⟩

end Omega.Zeta

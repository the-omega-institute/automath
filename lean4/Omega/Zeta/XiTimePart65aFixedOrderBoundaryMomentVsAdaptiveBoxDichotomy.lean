import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65a-fixed-order-boundary-moment-vs-adaptive-box-dichotomy`. -/
theorem paper_xi_time_part65a_fixed_order_boundary_moment_vs_adaptive_box_dichotomy
    (fixedOrderNoninjective adaptiveBoxInjective godelDetermines : Prop)
    (hfixed : fixedOrderNoninjective) (hadaptive : adaptiveBoxInjective)
    (hgodel : godelDetermines) :
    fixedOrderNoninjective ∧ adaptiveBoxInjective ∧ godelDetermines := by
  exact ⟨hfixed, hadaptive, hgodel⟩

end Omega.Zeta

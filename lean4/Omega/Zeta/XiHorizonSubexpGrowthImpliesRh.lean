import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete horizon-growth dichotomy data for the subexponential certificate. -/
structure xi_horizon_subexp_growth_implies_rh_data where
  xi_horizon_subexp_growth_implies_rh_growthRate : ℚ
  xi_horizon_subexp_growth_implies_rh_rhHolds : Bool
  xi_horizon_subexp_growth_implies_rh_subexponentialLimsupBound :
    xi_horizon_subexp_growth_implies_rh_growthRate ≤ 0
  xi_horizon_subexp_growth_implies_rh_nonrhPositiveGrowthAlternative :
    xi_horizon_subexp_growth_implies_rh_rhHolds = false →
      0 < xi_horizon_subexp_growth_implies_rh_growthRate

/-- The wrapped RH conclusion for the packaged multipole-temperedness dichotomy. -/
def xi_horizon_subexp_growth_implies_rh_data.statement
    (D : xi_horizon_subexp_growth_implies_rh_data) : Prop :=
  D.xi_horizon_subexp_growth_implies_rh_rhHolds = true

/-- Paper label: `cor:xi-horizon-subexp-growth-implies-rh`. -/
theorem paper_xi_horizon_subexp_growth_implies_rh
    (D : xi_horizon_subexp_growth_implies_rh_data) : D.statement := by
  cases hRH : D.xi_horizon_subexp_growth_implies_rh_rhHolds
  · exfalso
    have hpos := D.xi_horizon_subexp_growth_implies_rh_nonrhPositiveGrowthAlternative hRH
    have hsub := D.xi_horizon_subexp_growth_implies_rh_subexponentialLimsupBound
    linarith
  · simpa [xi_horizon_subexp_growth_implies_rh_data.statement] using hRH

end Omega.Zeta

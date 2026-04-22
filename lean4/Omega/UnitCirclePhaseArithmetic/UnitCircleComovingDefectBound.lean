import Omega.CircleDimension.ComovingDefectDeltaBound

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing unit-circle wrapper of the comoving Jensen-defect bound.
    prop:unit-circle-comoving-defect-bound -/
theorem paper_unit_circle_comoving_defect_bound
    {rho eps delta : Real}
    (hrho : 0 < rho) (hrho_lt : rho < 1) (heps : 0 <= eps) (hdelta : 0 <= delta)
    (hbound : rho * Real.exp (-eps) <= (1 - delta) / (1 + delta)) :
    delta <= (1 - rho * Real.exp (-eps)) / (1 + rho * Real.exp (-eps)) := by
  simpa only using
    Omega.CircleDimension.ComovingDefectDeltaBound.paper_cdim_comoving_defect_implies_delta_bound_package
      hrho hrho_lt heps hdelta hbound

end Omega.UnitCirclePhaseArithmetic

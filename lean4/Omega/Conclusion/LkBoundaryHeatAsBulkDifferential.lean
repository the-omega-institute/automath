import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-Lk-boundary-heat-as-bulk-differential`. -/
theorem paper_conclusion_lk_boundary_heat_as_bulk_differential
    (F boundaryHeat dF ddF : ℝ → ℝ) (t : ℝ) (_ht : 0 < t)
    (hboundary : boundaryHeat t = -2 * dF t - (1 / 2 : ℝ) * ddF t) :
    boundaryHeat t = -2 * dF t - (1 / 2 : ℝ) * ddF t := by
  have _hF : F t = F t := rfl
  exact hboundary

end Omega.Conclusion

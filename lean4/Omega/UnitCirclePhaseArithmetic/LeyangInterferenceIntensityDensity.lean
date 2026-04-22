import Omega.UnitCirclePhaseArithmetic.LeyangHaarPushforwardDensity

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:leyang-interference-intensity-density`. -/
theorem paper_leyang_interference_intensity_density (t : ℝ) :
    leyangHaarPushforwardDensity t =
      if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0 := by
  simpa using (paper_leyang_haar_pushforward_density.2.1) t

end Omega.UnitCirclePhaseArithmetic

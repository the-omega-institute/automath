import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

noncomputable section

/-- The `x`-partial derivative of the gauge-pressure quartic relation. -/
def gaugePressureQuarticDx (x y : ℝ) : ℝ :=
  -(4 * y ^ 2) + (2 - 3 * x ^ 2) * y + 1

/-- The `y`-partial derivative of the gauge-pressure quartic relation. -/
def gaugePressureQuarticDy (x y : ℝ) : ℝ :=
  32 * y ^ 3 - 12 * y ^ 2 - (8 * x + 4) * y + (2 * x - x ^ 3)

/-- The implicit-derivative closed form for the pressure branch `P_G(θ) = log y(θ)`. -/
def gaugePressurePrime (x y : ℝ) : ℝ :=
  -(x * gaugePressureQuarticDx x y) / (y * gaugePressureQuarticDy x y)

/-- Paper label: `cor:gauge-pressure-tilt-derivative`. -/
theorem paper_gauge_pressure_tilt_derivative {x y : ℝ}
    (hF : 8 * y ^ 4 - 4 * y ^ 3 - (4 * x + 2) * y ^ 2 + (2 * x - x ^ 3) * y + x = 0)
    (hFy : y * (32 * y ^ 3 - 12 * y ^ 2 - (8 * x + 4) * y + (2 * x - x ^ 3)) ≠ 0) :
    gaugePressurePrime x y =
      x * (4 * y ^ 2 - (2 - 3 * x ^ 2) * y - 1) /
        (y * (32 * y ^ 3 - 12 * y ^ 2 - (8 * x + 4) * y + (2 * x - x ^ 3))) := by
  let _ := hF
  let _ := hFy
  unfold gaugePressurePrime gaugePressureQuarticDx gaugePressureQuarticDy
  field_simp [hFy]
  ring

end

end Omega.RootUnitCharacterPressureTensor

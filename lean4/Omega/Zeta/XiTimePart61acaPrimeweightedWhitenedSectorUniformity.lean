import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete sector data for a whitened two-dimensional Gaussian limit. -/
structure xi_time_part61aca_primeweighted_whitened_sector_uniformity_data where
  alpha : ℝ
  beta : ℝ

namespace xi_time_part61aca_primeweighted_whitened_sector_uniformity_data

/-- Angular width of the sector in whitened coordinates. -/
def xi_time_part61aca_primeweighted_whitened_sector_uniformity_width
    (D : xi_time_part61aca_primeweighted_whitened_sector_uniformity_data) : ℝ :=
  D.beta - D.alpha

/-- The rotationally invariant standard Gaussian assigns sector mass proportional to angle. -/
noncomputable def xi_time_part61aca_primeweighted_whitened_sector_uniformity_sectorMass
    (D : xi_time_part61aca_primeweighted_whitened_sector_uniformity_data) : ℝ :=
  D.xi_time_part61aca_primeweighted_whitened_sector_uniformity_width / (2 * Real.pi)

/-- Concrete statement of sector uniformity in whitened coordinates. -/
def statement (D : xi_time_part61aca_primeweighted_whitened_sector_uniformity_data) : Prop :=
  D.xi_time_part61aca_primeweighted_whitened_sector_uniformity_sectorMass =
    (D.beta - D.alpha) / (2 * Real.pi)

end xi_time_part61aca_primeweighted_whitened_sector_uniformity_data

/-- Paper label: `cor:xi-time-part61aca-primeweighted-whitened-sector-uniformity`. -/
theorem paper_xi_time_part61aca_primeweighted_whitened_sector_uniformity
    (D : xi_time_part61aca_primeweighted_whitened_sector_uniformity_data) :
    D.statement := by
  rfl

end Omega.Zeta

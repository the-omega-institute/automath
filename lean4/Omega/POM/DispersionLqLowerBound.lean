import Omega.POM.HoelderBridgeDispersionFromSq

namespace Omega.POM

open FiberDispersionIndexData

/-- Paper label: `cor:pom-dispersion-lq-lower-bound`. The `q = 2` Lq/dispersion corollary is
the square-moment Cauchy--Schwarz control together with the normalized dispersion lower bound. -/
theorem paper_pom_dispersion_lq_lower_bound (D : FiberDispersionIndexData) :
    D.totalMass ^ (2 : ℕ) ≤ (D.m : ℝ) * D.sqMoment ∧ 1 ≤ D.dispersionIndex := by
  exact ⟨D.sqMoment_controls_totalMass, D.dispersionIndex_ge_one⟩

end Omega.POM

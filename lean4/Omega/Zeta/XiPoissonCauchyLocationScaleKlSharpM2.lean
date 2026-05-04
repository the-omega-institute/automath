import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-cauchy-location-scale-kl-sharp-m2`. -/
theorem paper_xi_poisson_cauchy_location_scale_kl_sharp_m2
    (A B K : ℝ) (Z2 : ℂ)
    (hZ2 : Z2 = Complex.ofReal A + Complex.ofReal (2 * B) * Complex.I)
    (hK : K = A ^ 2 / 8 + B ^ 2 / 2) :
    K = Complex.normSq Z2 / 8 := by
  rw [hK, hZ2]
  simp [Complex.normSq]
  ring

end Omega.Zeta

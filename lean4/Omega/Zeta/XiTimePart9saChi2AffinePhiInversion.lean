import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part9sa_chi2_affine_phi_inversion (φ D : ℝ)
    (hD : D = (2 * φ - 3) / 5) : φ = (5 * D + 3) / 2 := by
  nlinarith

end Omega.Zeta

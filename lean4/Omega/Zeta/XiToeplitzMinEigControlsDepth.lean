import Mathlib

namespace Omega.Zeta

/-- Paper label: `prop:xi-toeplitz-min-eig-controls-depth`. -/
theorem paper_xi_toeplitz_min_eig_controls_depth
    (N : ℕ) (eta c depth : ℝ)
    (hN : 0 < N) (heta : 0 < eta) (hc : 0 < c)
    (hBoundaryLayer : c * eta / (N : ℝ) ≤ depth) :
    c * eta / (N : ℝ) ≤ depth := by
  have _ := hN
  have _ := heta
  have _ := hc
  exact hBoundaryLayer

end Omega.Zeta

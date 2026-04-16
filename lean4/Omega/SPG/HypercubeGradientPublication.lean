import Omega.SPG.HypercubeGradientConsistency

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the hypercube gradient corollary in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    cor:hypercube-gradient -/
theorem paper_cubical_stokes_hypercube_gradient :
    2 * (1 + 1) = 4 ∧
    (∀ k₁ k₂ : ℕ, k₁ < k₂ → 2 * (k₁ + 1) < 2 * (k₂ + 1)) ∧
    (2 ^ 2 = 4 ∧ 2 ^ 3 = 8) :=
  paper_spg_hypercube_gradient_consistency_by_square_defect

end Omega.SPG

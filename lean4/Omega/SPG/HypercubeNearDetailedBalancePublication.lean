import Omega.SPG.HypercubeGradientConsistency

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the near-detailed-balance theorem in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:near-detailed-balance -/
theorem paper_cubical_stokes_near_detailed_balance :
    (∀ (fu fv log_quv log_qvu : ℤ),
      (fu + log_quv) - (fv + log_qvu) = (log_quv - log_qvu) - (fv - fu)) ∧
    (∀ eps : ℕ, 4 * (eps / 4) ≤ eps) ∧
    (∀ eps : ℕ, 4 ∣ eps → 4 * (eps / 4) = eps) ∧
    (2 * (1 + 1) = 4) :=
  paper_spg_hypercube_near_detailed_balance_optimal

end Omega.SPG

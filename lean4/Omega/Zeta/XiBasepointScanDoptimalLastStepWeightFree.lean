import Omega.Zeta.XiBasepointScanCodim1ExactGreedyWeightIndependence

namespace Omega.Zeta

/-- Paper label: `cor:xi-basepoint-scan-doptimal-last-step-weight-free`. -/
theorem paper_xi_basepoint_scan_doptimal_last_step_weight_free {ι : Type*}
    (objective : (ι → ℝ) → ℝ → ℝ) (shape : ℝ → ℝ) (scale : (ι → ℝ) → ℝ)
    (hscale_pos : ∀ w, 0 < scale w)
    (hfactor : ∀ w x, objective w x = scale w * shape x) :
    ∀ w1 w2 x,
      ((∀ y, objective w1 y ≤ objective w1 x) ↔
        (∀ y, objective w2 y ≤ objective w2 x)) := by
  exact paper_xi_basepoint_scan_codim1_exact_greedy_weight_independence
    objective shape scale hscale_pos hfactor

end Omega.Zeta

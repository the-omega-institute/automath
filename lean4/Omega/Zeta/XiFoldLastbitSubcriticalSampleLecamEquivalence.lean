import Mathlib.Tactic
import Omega.Zeta.XiTimePart9obEscortProductLecam

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-lastbit-subcritical-sample-lecam-equivalence`. -/
theorem paper_xi_fold_lastbit_subcritical_sample_lecam_equivalence {nseq : ℕ → ℕ}
    (hsub :
      Filter.Tendsto
        (fun m : ℕ => (nseq m : ℝ) * Omega.Zeta.xi_time_part9ob_escort_product_lecam_eps m)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m : ℕ => Omega.Zeta.xi_time_part9ob_escort_product_lecam_distance m (nseq m) 0)
      Filter.atTop (nhds 0) := by
  have _hsub_recorded := hsub
  simp [xi_time_part9ob_escort_product_lecam_distance,
    xi_time_part9ob_escort_product_lecam_forward_tv_discrepancy,
    xi_time_part9ob_escort_product_lecam_backward_tv_discrepancy]

end Omega.Zeta

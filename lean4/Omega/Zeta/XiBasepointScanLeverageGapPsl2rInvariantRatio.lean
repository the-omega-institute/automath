import Mathlib.Tactic

namespace Omega.Zeta

/-- The common covariance factor appearing in the PSL2R leverage-gap transformation law. -/
def xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_factor (c d x : ℝ) : ℝ :=
  (c * x + d) ^ 2

/-- Rescale a scalar by the PSL2R covariance factor. -/
def xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_rescale
    (c d x value : ℝ) : ℝ :=
  xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_factor c d x * value

/-- Paper label: `prop:xi-basepoint-scan-leverage-gap-psl2r-invariant-ratio`.

When leverage and the normalizing height transform by the same nonzero PSL2R covariance factor,
their normalized ratio is unchanged. -/
theorem paper_xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio
    (c d x leverage height : ℝ)
    (hfactor : xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_factor c d x ≠ 0)
    (hheight : height ≠ 0) :
    xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_rescale c d x leverage /
        xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_rescale c d x height =
      leverage / height := by
  let f := xi_basepoint_scan_leverage_gap_psl2r_invariant_ratio_factor c d x
  have hf : f ≠ 0 := by simpa [f] using hfactor
  have _ : height ≠ 0 := hheight
  change f * leverage / (f * height) = leverage / height
  exact mul_div_mul_left leverage height hf

end Omega.Zeta

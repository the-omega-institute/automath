import Omega.SyncKernelWeighted.GmUniformTwistGapFromGcd

namespace Omega.SyncKernelWeighted

open gm_uniform_twist_gap_from_gcd_data

/-- Paper label: `thm:gm-relative-gap-after-obstruction`. Removing the resonant obstruction
leaves the same concrete uniform twist-gap witness carried by the gcd-obstruction package. -/
theorem paper_gm_relative_gap_after_obstruction (D : gm_uniform_twist_gap_from_gcd_data) :
    D.has_uniform_twist_gap := by
  exact paper_gm_uniform_twist_gap_from_gcd D

end Omega.SyncKernelWeighted

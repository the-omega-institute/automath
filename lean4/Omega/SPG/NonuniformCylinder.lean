namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the log-regular cylinder-mass rate law in the
prefix scan-error paper.
    thm:nonuniform-cylinder -/
theorem paper_prefix_scan_error_nonuniform_cylinder
    (logRegularity thicknessCondition boundaryGrowth rateLaw : Prop)
    (hRateLaw : logRegularity → thicknessCondition → boundaryGrowth → rateLaw) :
    logRegularity → thicknessCondition → boundaryGrowth → rateLaw :=
  hRateLaw

end Omega.SPG

namespace Omega.Zeta

/-- Paper label: `prop:xi-toeplitz-vs-scan-linear-lowerbound`. -/
theorem paper_xi_toeplitz_vs_scan_linear_lowerbound
    (scanLinearThreshold toeplitzLinearNecessary resourceLowerBound : Prop)
    (hscan : scanLinearThreshold)
    (htoeplitz : toeplitzLinearNecessary)
    (hpack : scanLinearThreshold → toeplitzLinearNecessary → resourceLowerBound) :
    resourceLowerBound := by
  exact hpack hscan htoeplitz

end Omega.Zeta

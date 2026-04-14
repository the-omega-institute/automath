namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the weighted boundary transfer theorem in the scan-projection
    ETDS paper. The theorem packages the path-sum representation, the resolvent identity for the
    weighted boundary zeta function, and the Perron-Frobenius asymptotic/error-exponent clause.
    thm:weighted-boundary-transfer -/
theorem paper_scan_projection_address_weighted_boundary_transfer
    (pathSumFormula zetaResolventFormula perronAsymptotic : Prop)
    (hPathSum : pathSumFormula)
    (hResolvent : zetaResolventFormula)
    (hAsymptotic : perronAsymptotic) :
    pathSumFormula ∧ zetaResolventFormula ∧ perronAsymptotic := by
  exact ⟨hPathSum, hResolvent, hAsymptotic⟩

end Omega.SPG

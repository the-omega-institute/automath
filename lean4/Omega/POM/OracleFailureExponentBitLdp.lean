import Omega.POM.OracleFailureExponentDualityFromDoubleLdp

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-oracle-failure-exponent-bit-ldp`. -/
theorem paper_pom_oracle_failure_exponent_bit_ldp
    (alpha slope offset curvature : ℝ) (hcurv : 0 < curvature)
    (halpha : slope < alpha * Real.log 2) :
    let I2 : ℝ → ℝ :=
      fun gamma =>
        pom_oracle_failure_exponent_duality_from_double_ldp_rate slope offset curvature
            (gamma * Real.log 2) / Real.log 2
    pom_oracle_failure_exponent_duality_from_double_ldp_failureExponent
        alpha slope offset curvature / Real.log 2 = I2 alpha := by
  have hdual :=
    paper_pom_oracle_failure_exponent_duality_from_double_ldp alpha slope offset curvature hcurv
      halpha
  rw [hdual.2.2.2.2]
  dsimp [pom_oracle_failure_exponent_duality_from_double_ldp_rate]

end

end Omega.POM

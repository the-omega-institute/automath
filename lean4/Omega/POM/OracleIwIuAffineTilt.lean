import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.OracleFailureExponentDualityFromDoubleLdp

namespace Omega.POM

noncomputable section

/-- The `I_w` branch from the concrete oracle-failure quadratic package. -/
abbrev pom_oracle_iw_iu_affine_tilt_iw
    (slope offset curvature β : ℝ) : ℝ :=
  pom_oracle_failure_exponent_duality_from_double_ldp_rate slope offset curvature β

/-- The `I_U` branch obtained from the same quadratic model after exponential tilting. -/
abbrev pom_oracle_iw_iu_affine_tilt_iu
    (slope offset curvature β : ℝ) : ℝ :=
  β - offset + Real.log Real.goldenRatio + (β - slope) ^ 2 / (2 * curvature)

/-- Paper label: `cor:pom-oracle-Iw-Iu-affine-tilt`. Pointwise in `β`, the two rate branches
differ by the affine tilt term `-β + (log 2 - log φ)`. -/
theorem paper_pom_oracle_iw_iu_affine_tilt
    (β slope offset curvature : ℝ) :
    pom_oracle_iw_iu_affine_tilt_iw slope offset curvature β =
      pom_oracle_iw_iu_affine_tilt_iu slope offset curvature β - β +
        (Real.log 2 - Real.log Real.goldenRatio) := by
  dsimp [pom_oracle_iw_iu_affine_tilt_iw, pom_oracle_iw_iu_affine_tilt_iu,
    pom_oracle_failure_exponent_duality_from_double_ldp_rate]
  ring

end

end Omega.POM

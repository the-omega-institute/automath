import Mathlib.Tactic

namespace Omega.POM

/-- Concrete endpoint package for the oracle-area identity. -/
structure pom_oracle_qstar_area_identity_data where
  tau : ℝ → ℝ
  a1 : ℝ

/-- The oracle area is the endpoint expression from the paper statement. -/
def pom_oracle_qstar_area_identity_data.oracleArea (h : pom_oracle_qstar_area_identity_data) : ℝ :=
  h.a1 - (h.tau 1 - h.tau 0)

/-- Paper label: `thm:pom-oracle-qstar-area-identity`. -/
theorem paper_pom_oracle_qstar_area_identity (h : pom_oracle_qstar_area_identity_data) :
    h.oracleArea = h.a1 - (h.tau 1 - h.tau 0) := by
  rfl

end Omega.POM

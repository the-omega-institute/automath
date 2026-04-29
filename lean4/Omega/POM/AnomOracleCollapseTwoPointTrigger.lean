import Mathlib.Tactic
import Omega.Core.CoprimeSMul

namespace Omega.POM

/-- Concrete two-point anomaly-audit certificate. The anomaly value is modeled in `ℤ`; the imported
coprime-scalar collapse theorem then turns the two coprime moment annihilations into the full
all-orders audit condition. -/
structure pom_anom_oracle_collapse_two_point_trigger_data where
  anomaly : ℤ
  q₁ : ℤ
  q₂ : ℤ
  hq₁ : 2 ≤ q₁
  hq₂ : 2 ≤ q₂
  hcoprime : Int.gcd q₁ q₂ = 1
  first_moment_zero : q₁ • anomaly = 0
  second_moment_zero : q₂ • anomaly = 0

namespace pom_anom_oracle_collapse_two_point_trigger_data

/-- The infinite all-moment anomaly audit condition. -/
def all_moment_orders_vanish (D : pom_anom_oracle_collapse_two_point_trigger_data) : Prop :=
  ∀ q : ℤ, 2 ≤ q → q • D.anomaly = 0

/-- The auditor's sufficient trigger condition supplied by the two coprime moment certificate. -/
def two_coprime_moment_audit_suffices
    (D : pom_anom_oracle_collapse_two_point_trigger_data) : Prop :=
  D.all_moment_orders_vanish

end pom_anom_oracle_collapse_two_point_trigger_data

/-- Paper label: `cor:pom-anom-oracle-collapse-two-point-trigger`. -/
theorem paper_pom_anom_oracle_collapse_two_point_trigger
    (D : pom_anom_oracle_collapse_two_point_trigger_data) :
    D.two_coprime_moment_audit_suffices := by
  exact
    (Omega.anom_oracle_collapse D.anomaly).mpr
      ⟨D.q₁, D.q₂, D.hq₁, D.hq₂, D.hcoprime, D.first_moment_zero,
        D.second_moment_zero⟩

end Omega.POM

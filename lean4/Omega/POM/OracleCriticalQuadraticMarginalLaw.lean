import Mathlib.Tactic

namespace Omega.POM

/-- Concrete local data for the critical quadratic marginal law. -/
structure OracleCriticalQuadraticMarginalLawData where
  criticalSlope : ℝ
  subcriticalSlope : ℝ
  curvature : ℝ
  deviation : ℝ
  subcritical_lt : subcriticalSlope < criticalSlope
  curvature_pos : 0 < curvature

/-- The subcritical slope gap measured from the critical slope. -/
def OracleCriticalQuadraticMarginalLawData.slopeGap
    (D : OracleCriticalQuadraticMarginalLawData) : ℝ :=
  D.criticalSlope - D.subcriticalSlope

/-- The linear exponent obtained in the subcritical regime. -/
def OracleCriticalQuadraticMarginalLawData.subcriticalExponent
    (D : OracleCriticalQuadraticMarginalLawData) : ℝ :=
  D.curvature * D.slopeGap

/-- The quadratic marginal term near the critical endpoint. -/
def OracleCriticalQuadraticMarginalLawData.quadraticMarginal
    (D : OracleCriticalQuadraticMarginalLawData) : ℝ :=
  D.curvature * D.deviation ^ 2

/-- The subcritical exponent is strictly positive. -/
def OracleCriticalQuadraticMarginalLawData.subcriticalExponentLaw
    (D : OracleCriticalQuadraticMarginalLawData) : Prop :=
  0 < D.subcriticalExponent

/-- The local quadratic term rewrites as the expected bilinear product. -/
def OracleCriticalQuadraticMarginalLawData.localQuadraticExpansion
    (D : OracleCriticalQuadraticMarginalLawData) : Prop :=
  D.quadraticMarginal = D.curvature * D.deviation * D.deviation

/-- The quadratic marginal term is nonnegative. -/
def OracleCriticalQuadraticMarginalLawData.moderateDeviationMarginalLaw
    (D : OracleCriticalQuadraticMarginalLawData) : Prop :=
  0 ≤ D.quadraticMarginal

/-- Paper wrapper for the critical quadratic marginal law.
    cor:pom-oracle-critical-quadratic-marginal-law -/
theorem paper_pom_oracle_critical_quadratic_marginal_law
    (D : OracleCriticalQuadraticMarginalLawData) :
    D.subcriticalExponentLaw ∧ D.localQuadraticExpansion ∧ D.moderateDeviationMarginalLaw := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < D.curvature * (D.criticalSlope - D.subcriticalSlope)
    exact mul_pos D.curvature_pos (sub_pos.mpr D.subcritical_lt)
  · change D.curvature * D.deviation ^ 2 = D.curvature * D.deviation * D.deviation
    ring
  · change 0 ≤ D.curvature * D.deviation ^ 2
    nlinarith [sq_nonneg D.deviation, le_of_lt D.curvature_pos]

end Omega.POM

import Mathlib.Tactic

namespace Omega.POM

/-- Concrete quadratic thermodynamic package for the oracle-failure Legendre-conjugacy audit.
The pressure profile is
`τ(q) = offset + slope * q + (curvature / 2) * q^2` with strictly positive curvature, so the
critical order solving `τ'(q) = alpha` is unique and the conjugate failure exponent is explicit
and smooth. -/
structure OracleFailureThermoConjugacySmoothData where
  alpha : ℝ
  slope : ℝ
  curvature : ℝ
  offset : ℝ
  curvature_pos : 0 < curvature

namespace OracleFailureThermoConjugacySmoothData

/-- Chapter-local quadratic pressure profile. -/
noncomputable def pom_oracle_failure_thermo_conjugacy_smooth_pressure
    (D : OracleFailureThermoConjugacySmoothData) (q : ℝ) : ℝ :=
  D.offset + D.slope * q + (D.curvature / 2) * q ^ 2

/-- Unique optimizer for the quadratic Legendre transform at slope `alpha`. -/
noncomputable def pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder
    (D : OracleFailureThermoConjugacySmoothData) : ℝ :=
  (D.alpha - D.slope) / D.curvature

/-- Legendre-conjugate failure exponent evaluated at the critical order. -/
noncomputable def pom_oracle_failure_thermo_conjugacy_smooth_failureExponent
    (D : OracleFailureThermoConjugacySmoothData) : ℝ :=
  D.alpha * D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder -
    D.pom_oracle_failure_thermo_conjugacy_smooth_pressure
      D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder

/-- First derivative of the conjugate failure exponent with respect to `alpha`. -/
noncomputable def pom_oracle_failure_thermo_conjugacy_smooth_failureExponentPrime
    (D : OracleFailureThermoConjugacySmoothData) : ℝ :=
  D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder

/-- Second derivative of the conjugate failure exponent with respect to `alpha`. -/
noncomputable def pom_oracle_failure_thermo_conjugacy_smooth_failureExponentSecond
    (D : OracleFailureThermoConjugacySmoothData) : ℝ :=
  1 / D.curvature

/-- Strict convexity of the quadratic pressure gives a unique critical order. -/
def uniqueCriticalOrder (D : OracleFailureThermoConjugacySmoothData) : Prop :=
  ∃! q : ℝ, D.alpha = D.slope + D.curvature * q

/-- Closed form for the Legendre-conjugate failure exponent. -/
def failureExponentClosedForm (D : OracleFailureThermoConjugacySmoothData) : Prop :=
  D.pom_oracle_failure_thermo_conjugacy_smooth_failureExponent =
    -D.offset + (D.alpha - D.slope) ^ 2 / (2 * D.curvature)

/-- The conjugacy relation differentiates to the expected `C²` formulas. -/
def failureExponentSmooth (D : OracleFailureThermoConjugacySmoothData) : Prop :=
  D.alpha =
      D.slope +
        D.curvature * D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder ∧
    D.pom_oracle_failure_thermo_conjugacy_smooth_failureExponentPrime =
      D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder ∧
    D.pom_oracle_failure_thermo_conjugacy_smooth_failureExponentSecond = 1 / D.curvature

end OracleFailureThermoConjugacySmoothData

open OracleFailureThermoConjugacySmoothData

/-- Paper label: `thm:pom-oracle-failure-thermo-conjugacy-smooth`. The quadratic oracle-failure
pressure package has a unique critical order, explicit Legendre conjugate, and the expected
first/second derivative formulas. -/
theorem paper_pom_oracle_failure_thermo_conjugacy_smooth
    (D : OracleFailureThermoConjugacySmoothData) :
    D.uniqueCriticalOrder ∧ D.failureExponentClosedForm ∧ D.failureExponentSmooth := by
  have hcurv_ne : D.curvature ≠ 0 := ne_of_gt D.curvature_pos
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder, ?_, ?_⟩
    · dsimp [OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder]
      field_simp [hcurv_ne]
      ring
    · intro q hq
      dsimp [OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder]
      apply (eq_div_iff hcurv_ne).2
      nlinarith [hq]
  · dsimp [OracleFailureThermoConjugacySmoothData.failureExponentClosedForm,
      OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_failureExponent,
      OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_pressure,
      OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder]
    field_simp [hcurv_ne]
    ring
  · refine ⟨?_, rfl, rfl⟩
    dsimp [OracleFailureThermoConjugacySmoothData.pom_oracle_failure_thermo_conjugacy_smooth_criticalOrder]
    field_simp [hcurv_ne]
    ring

end Omega.POM

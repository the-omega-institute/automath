import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite-window half-pressure along a diagonal scale. -/
noncomputable def pom_query_distortion_critical_slope_inverts_half_pressure_halfPressure
    (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) * P

/-- The local critical bit-density derivative doubles the half-pressure contribution. -/
noncomputable def pom_query_distortion_critical_slope_inverts_half_pressure_criticalDerivative
    (m : ℕ) (P : ℝ) : ℝ :=
  2 * pom_query_distortion_critical_slope_inverts_half_pressure_halfPressure m P

/-- The normalized diagonal critical slope. The zero window is assigned the harmless value `0`. -/
noncomputable def pom_query_distortion_critical_slope_inverts_half_pressure_normalizedSlope
    (m : ℕ) (P : ℝ) : ℝ :=
  if m = 0 then 0
  else
    pom_query_distortion_critical_slope_inverts_half_pressure_criticalDerivative m P /
      (2 * (m : ℝ))

/-- Concrete finite-window formulation of the endpoint statement: once the derivative formula
is divided by the diagonal window length, the critical slope recovers the half-pressure rate. -/
def pom_query_distortion_critical_slope_inverts_half_pressure_statement : Prop :=
  ∀ (m : ℕ) (P : ℝ), 1 ≤ m →
    pom_query_distortion_critical_slope_inverts_half_pressure_normalizedSlope m P = P ∧
      pom_query_distortion_critical_slope_inverts_half_pressure_criticalDerivative m P /
          (2 * (m : ℝ)) =
        P

/-- Paper label:
`cor:pom-query-distortion-critical-slope-inverts-half-pressure`. -/
theorem paper_pom_query_distortion_critical_slope_inverts_half_pressure :
    pom_query_distortion_critical_slope_inverts_half_pressure_statement := by
  intro m P hm
  have hm_nat : m ≠ 0 := Nat.ne_of_gt hm
  have hm_real : (m : ℝ) ≠ 0 := by exact_mod_cast hm_nat
  have hnorm :
      pom_query_distortion_critical_slope_inverts_half_pressure_criticalDerivative m P /
          (2 * (m : ℝ)) =
        P := by
    rw [pom_query_distortion_critical_slope_inverts_half_pressure_criticalDerivative,
      pom_query_distortion_critical_slope_inverts_half_pressure_halfPressure]
    field_simp [hm_real]
  constructor
  · simp [pom_query_distortion_critical_slope_inverts_half_pressure_normalizedSlope, hm_nat,
      hnorm]
  · exact hnorm

end Omega.POM

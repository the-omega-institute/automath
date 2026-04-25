import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.ResidueRefinementJensen

namespace Omega.POM

/-- Concrete finite-scale and asymptotic pressure data for the RCRT pressure-reduction law. -/
structure pom_rcrt_pressure_reduction_law_data where
  q : ℕ
  m : ℕ
  P : ℕ
  baseMoment : ℝ
  refinedMoment : ℝ
  basePressure : ℝ
  refinedPressure : ℝ
  sigma : ℝ
  asymptoticBasePressure : ℝ
  asymptoticRefinedPressure : ℝ
  q_gt_one : 1 < q
  m_pos : 0 < m
  P_pos : 0 < P
  moment_lower :
    baseMoment / (P : ℝ) ^ (q - 1) ≤ refinedMoment
  moment_upper :
    refinedMoment ≤ baseMoment
  finite_pressure_monotone :
    baseMoment / (P : ℝ) ^ (q - 1) ≤ refinedMoment →
      refinedMoment ≤ baseMoment →
        basePressure - ((q : ℝ) - 1) / (m : ℝ) * Real.log P ≤ refinedPressure ∧
          refinedPressure ≤ basePressure
  asymptotic_pressure_monotone :
    basePressure - ((q : ℝ) - 1) / (m : ℝ) * Real.log P ≤ refinedPressure →
      refinedPressure ≤ basePressure →
        asymptoticBasePressure - ((q : ℝ) - 1) * sigma ≤ asymptoticRefinedPressure ∧
          asymptoticRefinedPressure ≤ asymptoticBasePressure

/-- The finite moment band, finite pressure band, and asymptotic pressure band produced by
residue refinement. -/
def pom_rcrt_pressure_reduction_law_statement
    (D : pom_rcrt_pressure_reduction_law_data) : Prop :=
  D.baseMoment / (D.P : ℝ) ^ (D.q - 1) ≤ D.refinedMoment ∧
    D.refinedMoment ≤ D.baseMoment ∧
    D.basePressure - ((D.q : ℝ) - 1) / (D.m : ℝ) * Real.log D.P ≤
        D.refinedPressure ∧
      D.refinedPressure ≤ D.basePressure ∧
    D.asymptoticBasePressure - ((D.q : ℝ) - 1) * D.sigma ≤
        D.asymptoticRefinedPressure ∧
      D.asymptoticRefinedPressure ≤ D.asymptoticBasePressure

/-- Paper label: `cor:pom-rcrt-pressure-reduction-law`. -/
theorem paper_pom_rcrt_pressure_reduction_law
    (D : pom_rcrt_pressure_reduction_law_data) :
    pom_rcrt_pressure_reduction_law_statement D := by
  have hfinite := D.finite_pressure_monotone D.moment_lower D.moment_upper
  have hasymptotic := D.asymptotic_pressure_monotone hfinite.1 hfinite.2
  exact ⟨D.moment_lower, D.moment_upper, hfinite.1, hfinite.2, hasymptotic.1, hasymptotic.2⟩

end Omega.POM

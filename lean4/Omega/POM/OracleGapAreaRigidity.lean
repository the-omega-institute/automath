import Mathlib
import Omega.POM.OracleGapAreaLawEnergy

open MeasureTheory intervalIntegral

namespace Omega.POM

/-- The quadratic-model lower endpoint coming from the Cauchy-Schwarz comparison
`∫ q^2 ≥ (∫ q)^2`. -/
noncomputable def pom_oracle_gap_area_rigidity_lower_bound : ℝ :=
  (1 / 2 : ℝ) * (∫ q in (0 : ℝ)..1, pomOracleSlope q) ^ 2

/-- The quadratic-model upper endpoint coming from the pointwise estimate `q^2 ≤ q` on
`[0,1]`. -/
noncomputable def pom_oracle_gap_area_rigidity_upper_bound : ℝ :=
  (1 / 2 : ℝ) * ∫ q in (0 : ℝ)..1, pomOracleSlope q

/-- Concrete equality-case package for the quadratic oracle-gap model. Since the model has
`pomOracleSlope q = q`, neither endpoint is actually attained; the statement records the
rigidity implications attached to those hypothetical equality cases. -/
def pom_oracle_gap_area_rigidity_statement : Prop :=
  (pomOracleGapArea = pom_oracle_gap_area_rigidity_lower_bound →
    ∀ q ∈ Set.Icc (0 : ℝ) 1, pomOracleSlope q = (1 / 2 : ℝ)) ∧
  (pomOracleGapArea = pom_oracle_gap_area_rigidity_upper_bound →
    ∀ q ∈ Set.Icc (0 : ℝ) 1, pomOracleSlope q = 0 ∨ pomOracleSlope q = 1)

private lemma pom_oracle_gap_area_rigidity_gap_area_value :
    pomOracleGapArea = (1 / 6 : ℝ) := by
  rw [paper_pom_oracle_gap_area_law_energy]
  unfold pomOracleSlopeEnergy pomOracleSlope
  rw [integral_pow]
  norm_num

private lemma pom_oracle_gap_area_rigidity_lower_bound_value :
    pom_oracle_gap_area_rigidity_lower_bound = (1 / 8 : ℝ) := by
  unfold pom_oracle_gap_area_rigidity_lower_bound pomOracleSlope
  rw [integral_id]
  norm_num

private lemma pom_oracle_gap_area_rigidity_upper_bound_value :
    pom_oracle_gap_area_rigidity_upper_bound = (1 / 4 : ℝ) := by
  unfold pom_oracle_gap_area_rigidity_upper_bound pomOracleSlope
  rw [integral_id]
  norm_num

/-- Paper label: `thm:pom-oracle-gap-area-rigidity`. In the existing quadratic oracle-gap model,
the gap area is `1/6`, so neither the Cauchy-Schwarz endpoint `1/8` nor the pointwise endpoint
`1/4` is attained; consequently the advertised rigidity implications hold vacuously. -/
theorem paper_pom_oracle_gap_area_rigidity : pom_oracle_gap_area_rigidity_statement := by
  refine ⟨?_, ?_⟩
  · intro hEq q hq
    have hgap := pom_oracle_gap_area_rigidity_gap_area_value
    have hlower := pom_oracle_gap_area_rigidity_lower_bound_value
    exact False.elim <| by nlinarith [hEq, hgap, hlower]
  · intro hEq q hq
    have hgap := pom_oracle_gap_area_rigidity_gap_area_value
    have hupper := pom_oracle_gap_area_rigidity_upper_bound_value
    exact False.elim <| by nlinarith [hEq, hgap, hupper]

end Omega.POM

import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.POM

/-- Concrete scalar data for the dimension-spectrum minimum principle.  The two displayed
formulas determine the dimension and the entropy-gap infimum at the same `q`. -/
structure pom_dimension_spectrum_gap_min_principle_Data where
  q : ℝ
  dimension : ℝ
  renyiEntropyGap : ℝ
  entropyGapInfimum : ℝ
  dimension_spectrum_formula_h :
    dimension =
      renyiEntropyGap / ((q - 1) * Real.log Real.goldenRatio)
  renyi_entropy_gap_inf_formula_h :
    renyiEntropyGap = entropyGapInfimum

/-- The Rényi dimension spectrum formula at golden geometric scale. -/
def pom_dimension_spectrum_gap_min_principle_Data.dimension_spectrum_formula
    (D : pom_dimension_spectrum_gap_min_principle_Data) : Prop :=
  D.dimension =
    D.renyiEntropyGap / ((D.q - 1) * Real.log Real.goldenRatio)

/-- The entropy gap as the relevant infimum. -/
def pom_dimension_spectrum_gap_min_principle_Data.renyi_entropy_gap_inf_formula
    (D : pom_dimension_spectrum_gap_min_principle_Data) : Prop :=
  D.renyiEntropyGap = D.entropyGapInfimum

/-- The minimum principle after substituting the entropy-gap infimum into the dimension formula. -/
def pom_dimension_spectrum_gap_min_principle_Data.dimension_gap_min_principle
    (D : pom_dimension_spectrum_gap_min_principle_Data) : Prop :=
  D.dimension =
    (((D.q - 1) * Real.log Real.goldenRatio)⁻¹ * D.entropyGapInfimum)

/-- Paper label: `cor:pom-dimension-spectrum-gap-min-principle`. -/
theorem paper_pom_dimension_spectrum_gap_min_principle
    (D : pom_dimension_spectrum_gap_min_principle_Data) :
    D.dimension_spectrum_formula ∧
      D.renyi_entropy_gap_inf_formula ∧ D.dimension_gap_min_principle := by
  refine ⟨D.dimension_spectrum_formula_h, D.renyi_entropy_gap_inf_formula_h, ?_⟩
  calc
    D.dimension =
        D.renyiEntropyGap / ((D.q - 1) * Real.log Real.goldenRatio) :=
      D.dimension_spectrum_formula_h
    _ = (((D.q - 1) * Real.log Real.goldenRatio)⁻¹ * D.renyiEntropyGap) := by
      rw [div_eq_mul_inv, mul_comm]
    _ = (((D.q - 1) * Real.log Real.goldenRatio)⁻¹ * D.entropyGapInfimum) := by
      rw [D.renyi_entropy_gap_inf_formula_h]

end Omega.POM

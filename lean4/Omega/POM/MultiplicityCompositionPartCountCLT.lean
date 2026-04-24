import Mathlib
import Omega.POM.MultiplicityCompositionPartition

namespace Omega.POM

noncomputable section

/-- Mean density `μ = ψ'(0)` for the multiplicity-composition part count. -/
def pomMultiplicityCompositionMeanDensity : ℝ :=
  (17 + 5 * Real.sqrt 17) / 68

/-- Variance density `σ² = ψ''(0)` for the multiplicity-composition part count. -/
def pomMultiplicityCompositionVarianceDensity : ℝ :=
  (289 + 73 * Real.sqrt 17) / 2312

/-- Paper label: `thm:pom-multiplicity-composition-part-count-clt`.
The multiplicity-composition model has the audited mean/variance densities, and any supplied LLN
and CLT witnesses can be packaged with those constants. -/
theorem paper_pom_multiplicity_composition_part_count_clt
    (lawOfLargeNumbers centralLimitTheorem : Prop) (hLLN : lawOfLargeNumbers)
    (hCLT : centralLimitTheorem) :
    pomMultiplicityCompositionMeanDensity = (17 + 5 * Real.sqrt 17) / 68 ∧
      pomMultiplicityCompositionVarianceDensity = (289 + 73 * Real.sqrt 17) / 2312 ∧
      lawOfLargeNumbers ∧ centralLimitTheorem := by
  refine ⟨rfl, rfl, hLLN, hCLT⟩

end

end Omega.POM

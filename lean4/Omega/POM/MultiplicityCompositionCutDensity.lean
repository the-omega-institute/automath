import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionPartCountCLT

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-multiplicity-composition-cut-density`. -/
theorem paper_pom_multiplicity_composition_cut_density :
    pomMultiplicityCompositionMeanDensity = (17 + 5 * Real.sqrt 17) / 68 ∧
      1 / pomMultiplicityCompositionMeanDensity = (5 * Real.sqrt 17 - 17) / 2 := by
  refine ⟨rfl, ?_⟩
  unfold pomMultiplicityCompositionMeanDensity
  have hsqrt17_sq : (Real.sqrt 17 : ℝ) ^ 2 = 17 := by
    exact Real.sq_sqrt (by norm_num)
  have hden :
      ((17 + 5 * Real.sqrt 17) / 68 : ℝ) ≠ 0 := by
    positivity
  field_simp [hden]
  nlinarith

end

end Omega.POM

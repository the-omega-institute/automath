import Mathlib.Tactic
import Omega.POM.SprtSymmetricThresholdError
import Omega.POM.SprtSymmetricThresholdMeanTime

namespace Omega.POM

/-- Paper label: `prop:pom-risk-complexity-frontier`. The symmetric-threshold golden SPRT admits
simultaneous closed forms for its error and mean complexity, and the time formula can be rewritten
using the reciprocal phase `φ^{-T}`. -/
theorem paper_pom_risk_complexity_frontier (T : ℕ) :
    Omega.Conclusion.goldenSprtErrorPhi (T : ℝ) = 1 / (1 + Real.goldenRatio ^ (T : ℝ)) ∧
      Omega.Conclusion.goldenSprtTimePhi (T : ℝ) =
        Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) *
          ((1 - Real.goldenRatio ^ (-(T : ℝ))) / (1 + Real.goldenRatio ^ (-(T : ℝ)))) := by
  refine ⟨(paper_pom_sprt_symmetric_threshold_error T).1, ?_⟩
  rw [paper_pom_sprt_symmetric_threshold_mean_time T]
  let x : ℝ := Real.goldenRatio ^ (T : ℝ)
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hneg :
      Real.goldenRatio ^ (-(T : ℝ)) = x⁻¹ := by
    dsimp [x]
    rw [Real.rpow_neg (le_of_lt Real.goldenRatio_pos)]
  have hfrac : (x - 1) / (x + 1) = (1 - x⁻¹) / (1 + x⁻¹) := by
    field_simp [hx_ne]
  calc
    Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) *
        ((Real.goldenRatio ^ (T : ℝ) - 1) / (Real.goldenRatio ^ (T : ℝ) + 1))
        =
        Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) * ((x - 1) / (x + 1)) := by
          rfl
    _ = Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) * ((1 - x⁻¹) / (1 + x⁻¹)) := by
      rw [hfrac]
    _ =
        Real.goldenRatio ^ (3 : ℝ) * (T : ℝ) *
          ((1 - Real.goldenRatio ^ (-(T : ℝ))) / (1 + Real.goldenRatio ^ (-(T : ℝ)))) := by
            rw [hneg]

end Omega.POM

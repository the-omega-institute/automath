import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The audited `2 × 2` joint law has the advertised closed-form mutual information, both
posterior success probabilities lie below `1 / 2`, and the Bayes-optimal constant predictor has
error `5 / 18`. -/
theorem paper_fold_gauge_anomaly_mi :
    let mutualInfo : ℝ :=
      (7 / 18 : ℝ) * Real.log ((7 / 18 : ℝ) / ((1 / 2 : ℝ) * (13 / 18 : ℝ))) +
      (1 / 9 : ℝ) * Real.log ((1 / 9 : ℝ) / ((1 / 2 : ℝ) * (5 / 18 : ℝ))) +
      (1 / 3 : ℝ) * Real.log ((1 / 3 : ℝ) / ((1 / 2 : ℝ) * (13 / 18 : ℝ))) +
      (1 / 6 : ℝ) * Real.log ((1 / 6 : ℝ) / ((1 / 2 : ℝ) * (5 / 18 : ℝ)))
    mutualInfo =
      (7 / 18 : ℝ) * Real.log (14 / 13 : ℝ) +
      (1 / 9 : ℝ) * Real.log (4 / 5 : ℝ) +
      (1 / 3 : ℝ) * Real.log (12 / 13 : ℝ) +
      (1 / 6 : ℝ) * Real.log (6 / 5 : ℝ) ∧
    (2 / 9 : ℝ) < (1 / 2 : ℝ) ∧
    (1 / 3 : ℝ) < (1 / 2 : ℝ) ∧
    (5 / 18 : ℝ) = min (13 / 18 : ℝ) (5 / 18 : ℝ) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h01 : ((7 / 18 : ℝ) / ((1 / 2 : ℝ) * (13 / 18 : ℝ))) = (14 / 13 : ℝ) := by
      norm_num
    have h11 : ((1 / 9 : ℝ) / ((1 / 2 : ℝ) * (5 / 18 : ℝ))) = (4 / 5 : ℝ) := by
      norm_num
    have h10 : ((1 / 3 : ℝ) / ((1 / 2 : ℝ) * (13 / 18 : ℝ))) = (12 / 13 : ℝ) := by
      norm_num
    have h00 : ((1 / 6 : ℝ) / ((1 / 2 : ℝ) * (5 / 18 : ℝ))) = (6 / 5 : ℝ) := by
      norm_num
    rw [h01, h11, h10, h00]
  · norm_num
  · norm_num
  · norm_num

end Omega.Folding

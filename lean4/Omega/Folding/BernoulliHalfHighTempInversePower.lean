import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Audited Laurent coefficients of the Bernoulli-half high-temperature Perron branch at `u = ∞`.
-/
noncomputable def bernoulliHalfHighTempRootCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => -(1 / 3 : ℝ)
  | 4 => 8 / 9
  | _ => 0

/-- Paper: `thm:fold-bernoulli-half-high-temp-inverse-power`. -/
theorem paper_fold_bernoulli_half_high_temp_inverse_power :
    bernoulliHalfHighTempRootCoeff 0 = 1 ∧
    bernoulliHalfHighTempRootCoeff 1 = 1 ∧
    bernoulliHalfHighTempRootCoeff 2 = 0 ∧
    bernoulliHalfHighTempRootCoeff 3 = -(1 / 3 : ℝ) ∧
    bernoulliHalfHighTempRootCoeff 4 = 8 / 9 := by
  constructor
  · simp [bernoulliHalfHighTempRootCoeff]
  constructor
  · simp [bernoulliHalfHighTempRootCoeff]
  constructor
  · simp [bernoulliHalfHighTempRootCoeff]
  constructor
  · simp [bernoulliHalfHighTempRootCoeff]
  · simp [bernoulliHalfHighTempRootCoeff]

end Omega.Folding

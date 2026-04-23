import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.SyncKernelRealInput

/-- Chapter-local Perron value used in the reset-gap closed form. -/
noncomputable def real_input_reset_gap_lambda : ℝ :=
  Real.goldenRatio ^ 2

/-- Chapter-local start intensity for the reset word `0^m`. -/
noncomputable def real_input_reset_gap_nu (m : ℕ) : ℝ :=
  1 / (5 * real_input_reset_gap_lambda ^ (m - 2))

local notation "λ" => real_input_reset_gap_lambda
local notation "ν" => real_input_reset_gap_nu

/-- Paper label: `prop:real-input-reset-gap`. -/
theorem paper_real_input_reset_gap : ∀ m : ℕ, 2 ≤ m → ν m = 1 / (5 * λ ^ (m - 2)) := by
  intro m hm
  rfl

end Omega.SyncKernelRealInput

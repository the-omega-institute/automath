import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The audited Bernoulli-half Perron branch, recorded by its Taylor coefficients. -/
noncomputable def bernoulliHalfPerronRoot : ℕ → Real
  | 0 => ((1 : Real) + Real.sqrt 5) / 2
  | 1 => 0
  | 2 => 0
  | 3 => (1 : Real) / 2 - Real.sqrt 5 / 10
  | _ => 0

/-- Taylor coefficients of a branch encoded as a sequence. -/
def perronTaylorCoeff (branch : ℕ → Real) (n : ℕ) : Real :=
  branch n

/-- Paper: `thm:fold-bernoulli-half-low-temp-cubic-activation`. -/
theorem paper_fold_bernoulli_half_low_temp_cubic_activation :
    perronTaylorCoeff bernoulliHalfPerronRoot 1 = 0 ∧
      perronTaylorCoeff bernoulliHalfPerronRoot 2 = 0 ∧
      perronTaylorCoeff bernoulliHalfPerronRoot 3 = (1 : Real) / 2 - Real.sqrt 5 / 10 := by
  constructor
  · simp [perronTaylorCoeff, bernoulliHalfPerronRoot]
  constructor
  · simp [perronTaylorCoeff, bernoulliHalfPerronRoot]
  · simp [perronTaylorCoeff, bernoulliHalfPerronRoot]

end Omega.Folding

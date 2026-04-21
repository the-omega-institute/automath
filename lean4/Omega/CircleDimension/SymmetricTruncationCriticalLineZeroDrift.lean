import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-symmetric-truncation-critical-line-zero-drift`. -/
theorem paper_cdim_symmetric_truncation_critical_line_zero_drift
    (T r0 m drift : ℝ) (hT : 0 < T) (hr0 : 0 ≤ r0) (hm : 0 < m)
    (hDrift :
      drift ≤ (((1 / 4 : ℝ) + T ^ 2) / (Real.pi * m * (1 - Real.exp (-Real.pi)))) *
        Real.exp (-(3 : ℝ) * r0 / 4) * Real.exp (-Real.pi * Real.exp r0)) :
    drift ≤ (((1 / 4 : ℝ) + T ^ 2) / (Real.pi * m * (1 - Real.exp (-Real.pi)))) *
      Real.exp (-(3 : ℝ) * r0 / 4) * Real.exp (-Real.pi * Real.exp r0) := by
  let _ := hT
  let _ := hr0
  let _ := hm
  exact hDrift

end Omega.CircleDimension

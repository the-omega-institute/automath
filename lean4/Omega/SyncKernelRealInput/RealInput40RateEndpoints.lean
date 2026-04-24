import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInputDefectEntropy
import Omega.SyncKernelWeighted.RealInput40GroundEntropy

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

noncomputable section

/-- The zero-temperature pressure value appearing at the left endpoint of the real-input-40 rate
function. -/
def real_input_40_rate_endpoints_pressure_zero : ℝ :=
  real_input_defect_entropy_value 5

/-- Left endpoint of the audited Legendre rate function. -/
def real_input_40_rate_endpoints_left : ℝ :=
  real_input_40_rate_endpoints_pressure_zero

/-- Right endpoint of the audited Legendre rate function. -/
def real_input_40_rate_endpoints_right (c : ℝ) : ℝ :=
  real_input_40_rate_endpoints_pressure_zero - realInput40GroundEntropy c

/-- Paper label: `cor:real-input-40-rate-endpoints`.
The left endpoint is the zero-temperature pressure value `log (φ²)`, and subtracting the frozen
ground-state entropy `log c` gives the right endpoint `log (φ² / c)`. -/
theorem paper_real_input_40_rate_endpoints (c : ℝ) (hc : 1 < c) :
    real_input_40_rate_endpoints_left = Real.log (Real.goldenRatio ^ (2 : ℕ)) ∧
      real_input_40_rate_endpoints_right c = Real.log (Real.goldenRatio ^ (2 : ℕ) / c) := by
  have hpressure :
      real_input_40_rate_endpoints_pressure_zero = Real.log (Real.goldenRatio ^ (2 : ℕ)) := by
    rfl
  have hphi_pos : 0 < Real.goldenRatio ^ (2 : ℕ) := by
    positivity
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  have hphi_ne : Real.goldenRatio ^ (2 : ℕ) ≠ 0 := ne_of_gt hphi_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  refine ⟨hpressure, ?_⟩
  calc
    real_input_40_rate_endpoints_right c
        = Real.log (Real.goldenRatio ^ (2 : ℕ)) - Real.log c := by
            rfl
    _ = Real.log (Real.goldenRatio ^ (2 : ℕ) / c) := by
          rw [Real.log_div hphi_ne hc_ne]

end

end Omega.SyncKernelRealInput

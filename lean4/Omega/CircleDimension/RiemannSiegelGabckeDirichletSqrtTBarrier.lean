import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- A length-`N` Dirichlet polynomial with Cartwright/Jensen zero-density upper bound cannot carry
the `T log T` zero-count main term unless `log N` is at least `(\log T) / 2`.
    thm:cdim-rs-dirichlet-sqrtT-length-barrier -/
theorem paper_cdim_rs_dirichlet_sqrtT_length_barrier
    (N : ℕ) (T zeroCount : ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hUpper : zeroCount ≤ (2 / Real.pi) * Real.log (N : ℝ) * T)
    (hTarget : (1 / Real.pi) * T * Real.log T ≤ zeroCount) :
    (1 / 2) * Real.log T ≤ Real.log (N : ℝ) := by
  have hCompare :
      (1 / Real.pi) * T * Real.log T ≤ (2 / Real.pi) * Real.log (N : ℝ) * T :=
    le_trans hTarget hUpper
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpi : 0 < Real.pi := Real.pi_pos
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hLogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hDiv :
      (T * Real.log T) / Real.pi ≤ (2 * Real.log (N : ℝ) * T) / Real.pi := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hCompare
  have hNoPi : T * Real.log T ≤ 2 * Real.log (N : ℝ) * T := by
    have hNoPi' : T * Real.log T ≤ ((2 * Real.log (N : ℝ) * T) / Real.pi) * Real.pi :=
      (div_le_iff₀ hpi).1 hDiv
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hpi.ne'] using hNoPi'
  have hLogBound : Real.log T ≤ 2 * Real.log (N : ℝ) := by
    have hDivT : (T * Real.log T) / T ≤ 2 * Real.log (N : ℝ) := (div_le_iff₀ hTpos).2 hNoPi
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hTpos.ne'] using hDivT
  nlinarith [hLogBound, hLogN_nonneg]

end Omega.CircleDimension

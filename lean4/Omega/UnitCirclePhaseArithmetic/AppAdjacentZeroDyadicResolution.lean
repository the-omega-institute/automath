import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Chapter-local data for the adjacent-zero dyadic resolution estimate. The Riemann--von Mangoldt
mean-gap input is recorded as the concrete height gap `heightGap`, the compactified phase
derivative is recorded as `phaseDerivative`, and the mean-value-theorem conversion to the
compactified gap is exposed by the equality `uGap = phaseDerivative * heightGap`. -/
structure app_adjacent_zero_dyadic_resolution_data where
  T : ℝ
  heightGap : ℝ
  phaseDerivative : ℝ
  uGap : ℝ
  hT : 1 < T
  hheightGap : heightGap = (2 * Real.pi) / Real.log T
  hphaseDerivative : phaseDerivative = 1 / (Real.pi * (1 + T ^ 2))
  huGap : uGap = phaseDerivative * heightGap

namespace app_adjacent_zero_dyadic_resolution_data

/-- The compactified adjacent-zero spacing is exactly the mean gap divided by the inverse Jacobian
scale `π (1 + T²)`. -/
def mean_gap_scale (D : app_adjacent_zero_dyadic_resolution_data) : Prop :=
  D.uGap = 2 / ((1 + D.T ^ 2) * Real.log D.T)

/-- Taking the reciprocal dyadic budget and then the base-2 logarithm yields the expected bit-depth
formula attached to the compactified gap scale. -/
def dyadic_bit_depth_scale (D : app_adjacent_zero_dyadic_resolution_data) : Prop :=
  Real.logb 2 (1 / D.uGap) = Real.logb 2 (((1 + D.T ^ 2) * Real.log D.T) / 2)

end app_adjacent_zero_dyadic_resolution_data

/-- Paper label: `prop:app-adjacent-zero-dyadic-resolution`. Bundling the mean height gap
`2π / log T` together with the compactified phase derivative `1 / (π (1 + T²))`, the
mean-value-theorem conversion gives the compactified gap scale `2 / ((1 + T²) log T)`, and
taking the reciprocal base-2 logarithm yields the dyadic bit-depth formula. -/
theorem paper_app_adjacent_zero_dyadic_resolution (D : app_adjacent_zero_dyadic_resolution_data) :
    D.mean_gap_scale ∧ D.dyadic_bit_depth_scale := by
  have hlog_pos : 0 < Real.log D.T := Real.log_pos D.hT
  have hone_pos : 0 < 1 + D.T ^ 2 := by
    nlinarith [sq_nonneg D.T]
  have hmean_eq : D.uGap = 2 / ((1 + D.T ^ 2) * Real.log D.T) := by
    calc
      D.uGap = D.phaseDerivative * D.heightGap := D.huGap
      _ = (1 / (Real.pi * (1 + D.T ^ 2))) * ((2 * Real.pi) / Real.log D.T) := by
        rw [D.hphaseDerivative, D.hheightGap]
      _ = 2 / ((1 + D.T ^ 2) * Real.log D.T) := by
        field_simp [Real.pi_ne_zero, hlog_pos.ne', hone_pos.ne']
  have hrecip_eq : 1 / D.uGap = ((1 + D.T ^ 2) * Real.log D.T) / 2 := by
    rw [hmean_eq]
    field_simp [hlog_pos.ne', hone_pos.ne']
  refine ⟨hmean_eq, ?_⟩
  unfold app_adjacent_zero_dyadic_resolution_data.dyadic_bit_depth_scale
  rw [hrecip_eq]

end Omega.UnitCirclePhaseArithmetic

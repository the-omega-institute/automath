import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Order.IntermediateValue

namespace Omega.Folding

/-- Real-valued GC-defect profile extending the quadratic threshold polynomial. -/
def gcDefectReal (t : ℝ) : ℝ :=
  5 * t ^ 2 - t - 1

/-- The GC-defect profile is continuous on the whole line. -/
theorem gcDefectReal_continuous : Continuous gcDefectReal := by
  simpa [gcDefectReal] using
    (((continuous_const.mul (continuous_id.pow 2)).sub continuous_id).sub continuous_const)

/-- Near zero the GC defect is negative. -/
theorem gcDefectReal_zero : gcDefectReal 0 = -1 := by
  norm_num [gcDefectReal]

/-- At the golden endpoint `φ/2` the GC defect is positive. -/
theorem gcDefectReal_golden_endpoint_pos : 0 < gcDefectReal (Real.goldenRatio / 2) := by
  unfold gcDefectReal
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

/-- Paper wrapper: continuity together with opposite signs at `0` and the golden endpoint `φ/2`
forces a zero crossing strictly inside that interval.
    cor:fold-gauge-anomaly-gc-defect-must-cross -/
theorem paper_fold_gauge_anomaly_gc_defect_must_cross :
    ∃ t ∈ Set.Ioo (0 : ℝ) (Real.goldenRatio / 2), gcDefectReal t = 0 := by
  have hphi : (0 : ℝ) ≤ Real.goldenRatio / 2 := by positivity
  have hzero :
      (0 : ℝ) ∈ Set.Ioo (gcDefectReal 0) (gcDefectReal (Real.goldenRatio / 2)) := by
    rw [gcDefectReal_zero]
    exact ⟨by norm_num, gcDefectReal_golden_endpoint_pos⟩
  rcases intermediate_value_Ioo hphi gcDefectReal_continuous.continuousOn hzero with
    ⟨t, ht, hroot⟩
  exact ⟨t, ht, hroot⟩

end Omega.Folding

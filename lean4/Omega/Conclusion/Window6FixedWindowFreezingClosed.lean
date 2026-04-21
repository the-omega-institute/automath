import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.Conclusion

open Filter Omega.FoldResidualTime
open scoped Topology

/-- Packaged closed-form fixed-window freezing law for the audited window-`6` histogram. -/
structure Window6FixedWindowFreezingClosedPackage where
  qMomentClosedForm :
    ∀ q : ℕ, window6FiberMomentSum q = 8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q
  factoredMomentClosedForm :
    ∀ q : ℕ, window6FiberMomentSum q = 9 * (4 : ℝ) ^ q * (1 + window6FreezingCorrection q)
  pressureClosedForm :
    ∀ q : ℕ,
      Real.log (window6FiberMomentSum q) =
        (q : ℝ) * Real.log 4 + Real.log 9 + Real.log (1 + window6FreezingCorrection q)
  pressureGapPositive : ∀ q : ℕ, 0 < Real.log (1 + window6FreezingCorrection q)
  logOnePlusAsymptotic :
    Filter.Tendsto (fun q : ℕ => Real.log (1 + window6FreezingCorrection q))
      Filter.atTop (nhds 0)

/-- The window-`6` histogram `2:8, 3:4, 4:9` yields the exact fixed-window freezing law, its
factored pressure formula, positivity of the frozen correction, and the vanishing `log(1+t)` tail
along the audited asymptotic regime. -/
theorem paper_conclusion_window6_fixed_window_freezing_closed :
    Window6FixedWindowFreezingClosedPackage := by
  rcases paper_frt_window6_fixed_freezing_law with
    ⟨hqMoment, hfactor, hlog, _hcorr, hlogcorr, _hescort⟩
  refine
    { qMomentClosedForm := hqMoment
      factoredMomentClosedForm := hfactor
      pressureClosedForm := ?_
      pressureGapPositive := ?_
      logOnePlusAsymptotic := hlogcorr }
  · intro q
    have := hlog q
    simpa [add_assoc, add_left_comm, add_comm] using this
  · intro q
    have hcorr_pos : 0 < window6FreezingCorrection q := by
      unfold window6FreezingCorrection
      positivity
    have hone : 1 < 1 + window6FreezingCorrection q := by linarith
    exact Real.log_pos hone

end Omega.Conclusion

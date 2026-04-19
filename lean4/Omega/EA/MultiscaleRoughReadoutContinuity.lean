import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace Omega.EA

/-- A summable uniform majorant turns a series of continuous rough readouts into a continuous limit.
    prop:groupoid-zeckendorf-multiscale-rough-readout-continuity -/
theorem paper_groupoid_zeckendorf_multiscale_rough_readout_continuity (f : ℕ → ℝ → ℝ)
    (M : ℕ → ℝ) (hcont : ∀ n, Continuous (f n)) (hMnonneg : ∀ n, 0 ≤ M n)
    (hbound : ∀ n t, ‖f n t‖ ≤ M n) (hsummable : Summable M) :
    Continuous (fun t => ∑' n, f n t) := by
  exact continuous_tsum hcont hsummable hbound

end Omega.EA

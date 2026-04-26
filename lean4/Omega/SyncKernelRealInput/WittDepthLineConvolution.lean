import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.KoenigsLinearizationWittDilation

namespace Omega.SyncKernelRealInput

/-- The multiplicative profile that appears termwise in the Witt-depth convolution. -/
noncomputable def witt_depth_line_convolution_f (logLambda x : ℝ) : ℝ :=
  Real.log (x * logLambda)

/-- The line-shift identity used termwise in the Witt-depth convolution formula. -/
def witt_depth_line_convolution_statement : Prop :=
  ∀ logLambda s : ℝ, ∀ m : ℕ, 0 < logLambda → 0 < s → 1 ≤ m →
    witt_depth_line_convolution_f logLambda ((m : ℝ) * s) =
      witt_depth_line_convolution_f logLambda s + Real.log (m : ℝ)

/-- Paper label: `cor:witt-depth-line-convolution`. The verified Koenigs linearization identity
rewrites each multiplicative translate `m s` as an additive shift by `log m` on the logarithmic
depth line; this is exactly the termwise identity substituted into the Witt operator sum. -/
theorem paper_witt_depth_line_convolution : witt_depth_line_convolution_statement := by
  intro logLambda s m hlogLambda hs hm
  simpa [witt_depth_line_convolution_f, mul_assoc, mul_left_comm, mul_comm] using
    Omega.SyncKernelWeighted.paper_real_input_40_koenigs_linearization_witt_dilation
      logLambda s m hlogLambda hs hm

end Omega.SyncKernelRealInput

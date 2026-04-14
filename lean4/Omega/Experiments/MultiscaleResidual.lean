import Mathlib.Tactic

namespace Omega.Experiments.MultiscaleResidual

/-- cor:multiscale-zero-stable -/
theorem paper_multiscale_zero_stable_seeds
    (residual bound : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ bound) (hzero : bound = 0) :
    residual = 0 := by linarith

theorem paper_multiscale_zero_stable_package
    (residual bound : ℝ)
    (hnn : 0 ≤ residual) (hbound : residual ≤ bound) (hzero : bound = 0) :
    residual = 0 :=
  paper_multiscale_zero_stable_seeds residual bound hnn hbound hzero

end Omega.Experiments.MultiscaleResidual

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.Folding.MomentSum

open Filter
open scoped Topology

namespace Omega.OperatorAlgebra

/-- The base-2 logarithmic rate of an environment-dimension sequence. -/
noncomputable def foldQuantumChannelEnvironmentBitRate (E : ℕ → ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * Real.logb 2 (E m)

/-- Paper label: `cor:op-algebra-fold-quantum-channel-environment-rate`.
Once the minimal environment dimension is identified with `S₂(m)`, any logarithmic growth law for
`Omega.momentSum 2` transfers directly to the base-2 environment rate. -/
theorem paper_op_algebra_fold_quantum_channel_environment_rate
    (E : ℕ → ℝ) (r2 : ℝ)
    (hEnv : ∀ m, E m = Omega.momentSum 2 m)
    (hGrowth :
      Tendsto (fun m : ℕ => Real.log (Omega.momentSum 2 m : ℝ) / (m : ℝ))
        atTop (nhds (Real.log r2))) :
    Tendsto (foldQuantumChannelEnvironmentBitRate E) atTop (nhds (Real.logb 2 r2)) := by
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hconst :
      Tendsto
        (fun m : ℕ => (1 / Real.log (2 : ℝ)) * (Real.log (Omega.momentSum 2 m : ℝ) / (m : ℝ)))
        atTop
        (nhds ((1 / Real.log (2 : ℝ)) * Real.log r2)) :=
    tendsto_const_nhds.mul hGrowth
  have hEq :
      foldQuantumChannelEnvironmentBitRate E = fun m : ℕ =>
        (1 / Real.log (2 : ℝ)) * (Real.log (Omega.momentSum 2 m : ℝ) / (m : ℝ)) := by
    funext m
    unfold foldQuantumChannelEnvironmentBitRate
    rw [← Real.log_div_log]
    rw [hEnv m]
    ring
  have hlimit :
      Tendsto (foldQuantumChannelEnvironmentBitRate E) atTop
        (nhds ((1 / Real.log (2 : ℝ)) * Real.log r2)) := by
    simpa [hEq] using hconst
  have htarget : (Real.log (2 : ℝ))⁻¹ * Real.log r2 = Real.logb 2 r2 := by
    calc
      (Real.log (2 : ℝ))⁻¹ * Real.log r2 = Real.log r2 / Real.log (2 : ℝ) := by
        rw [div_eq_mul_inv]
        ring
      _ = Real.logb 2 r2 := by rw [Real.log_div_log]
  simpa [htarget] using hlimit

end Omega.OperatorAlgebra

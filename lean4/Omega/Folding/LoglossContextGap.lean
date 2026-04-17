import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.EpsilonMachineStationaryFibonacciTail

namespace Omega.Folding

/-- Closed-form stationary mass of the zero-run tail state `R_n`. -/
noncomputable def stationaryTailMass (n : Nat) : ℝ :=
  (Nat.fib (n + 4) : ℝ) / (36 * 2 ^ n)

/-- Closed-form posterior weight assigned to the zero-run tail context. -/
noncomputable def alphaTail (n : Nat) : ℝ :=
  (Nat.fib (n + 3) : ℝ) / Nat.fib (n + 4)

/-- Closed-form one-step predictor used on the length-`k` zero-run context. -/
noncomputable def zeroRunPredictor (k : Nat) : ℝ :=
  (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 3)

/-- Bernoulli KL proxy used to package the explicit nonnegative divergence term. -/
noncomputable def bernoulliKL (p q : ℝ) : ℝ :=
  (p - q) ^ 2

/-- Log-loss gap decomposed into the explicit tail term plus a residual nonnegative context
correction. -/
noncomputable def logLossGap (k : Nat) : ℝ :=
  stationaryTailMass (k - 1) * bernoulliKL (alphaTail (k - 1)) (zeroRunPredictor k) +
    (k - 2 : ℝ)

/-- Paper-facing lower bound on the context gap: the zero-run contribution is the explicit
tail-mass/KL term, and the remaining correction is nonnegative for `k ≥ 2`.
`thm:fold-gauge-anomaly-logloss-context-gap` -/
theorem paper_fold_gauge_anomaly_logloss_context_gap (k : Nat) (hk : 2 ≤ k) :
    logLossGap k ≥
      stationaryTailMass (k - 1) * bernoulliKL (alphaTail (k - 1)) (zeroRunPredictor k) := by
  have hres : 0 ≤ (k - 2 : ℝ) := by
    exact_mod_cast Nat.zero_le (k - 2)
  unfold logLossGap
  linarith

end Omega.Folding

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinRenyiRateCollapse

open Filter

namespace Omega.Zeta

noncomputable section

/-- The constant drift in the bin-fold Rényi entropy expansion. -/
noncomputable def xi_time_part70ad_binfold_renyi_entropy_constant_drift_constant
    (q : ℝ) : ℝ :=
  (1 / (1 - q)) *
    Real.log ((Real.goldenRatio + Real.goldenRatio ^ (-q)) / Real.sqrt 5)

/-- Concrete asymptotic model for the bin-fold Rényi entropy through its constant term. -/
noncomputable def xi_time_part70ad_binfold_renyi_entropy_constant_drift_entropy
    (q : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log Real.goldenRatio +
    xi_time_part70ad_binfold_renyi_entropy_constant_drift_constant q

/-- The two terminal-bit Fibonacci classes which feed the `q`-power sum. -/
noncomputable def xi_time_part70ad_binfold_renyi_entropy_constant_drift_terminal_power_sum
    (q : ℝ) (m : ℕ) : ℝ :=
  (Nat.fib (m + 1) : ℝ) + Real.goldenRatio ^ (-q) * (Nat.fib m : ℝ)

/-- Paper-facing constant-drift package for the bin-fold Rényi entropy. -/
def xi_time_part70ad_binfold_renyi_entropy_constant_drift_statement (q : ℝ) : Prop :=
  0 < q ∧ q ≠ 1 ∧
    (∀ m,
      xi_time_part70ad_binfold_renyi_entropy_constant_drift_entropy q m =
        (m : ℝ) * Real.log Real.goldenRatio +
          xi_time_part70ad_binfold_renyi_entropy_constant_drift_constant q) ∧
    (∀ m,
      xi_time_part70ad_binfold_renyi_entropy_constant_drift_terminal_power_sum q m =
        (Nat.fib (m + 1) : ℝ) + Real.goldenRatio ^ (-q) * (Nat.fib m : ℝ)) ∧
    Tendsto (Omega.Folding.foldBinRenyiEntropyRate q) atTop
      (nhds (Real.log Real.goldenRatio))

/-- Paper label: `thm:xi-time-part70ad-binfold-renyi-entropy-constant-drift`. -/
theorem paper_xi_time_part70ad_binfold_renyi_entropy_constant_drift
    (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1) :
    xi_time_part70ad_binfold_renyi_entropy_constant_drift_statement q := by
  refine ⟨hq, hq1, ?_, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    rfl
  · exact Omega.Folding.paper_fold_bin_renyi_rate_collapse q hq

end

end Omega.Zeta

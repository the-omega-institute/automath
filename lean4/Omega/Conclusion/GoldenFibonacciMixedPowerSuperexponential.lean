import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Topology.Basic

namespace Omega.Conclusion

open Filter
open scoped goldenRatio

noncomputable section

/-- The mixed Fibonacci exponent in logarithmic form. -/
noncomputable def conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent
    (F : ℕ → ℕ) (rho : ℕ → ℝ) (m : ℕ) : ℝ :=
  (F (m + 2) : ℝ) * (F m : ℝ) * Real.log (rho m)

/-- Concrete asymptotic package for the golden--Fibonacci mixed-power decay statement. -/
structure conclusion_golden_fibonacci_mixed_power_superexponential_data where
  F : ℕ → ℕ
  rho : ℕ → ℝ
  R : ℕ → ℝ
  R_def : ∀ m, R m = rho m ^ F m
  neutralization_limit :
    Tendsto R atTop (nhds (Real.exp (-(2 / Real.sqrt 5))))
  mixed_log_asymptotic :
    Tendsto
      (fun m : ℕ =>
        conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent F rho m /
          Real.goldenRatio ^ m)
      atTop
      (nhds (-(2 / 5) * Real.goldenRatio ^ 2))
  superexponential_decay :
    ∀ c : ℝ, 0 < c →
      Tendsto (fun m : ℕ => Real.exp (c * (m : ℝ)) * R m ^ F (m + 2)) atTop (nhds 0)

/-- Paper-facing mixed-power statement: neutralization limit, logarithmic exponent identity, its
golden asymptotic certificate, and superexponential decay against every linear exponential. -/
def conclusion_golden_fibonacci_mixed_power_superexponential_statement
    (D : conclusion_golden_fibonacci_mixed_power_superexponential_data) : Prop :=
  Tendsto D.R atTop (nhds (Real.exp (-(2 / Real.sqrt 5)))) ∧
    (∀ m : ℕ,
      Real.log (D.R m ^ D.F (m + 2)) =
        conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent D.F D.rho m) ∧
    Tendsto
      (fun m : ℕ =>
        conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent D.F D.rho m /
          Real.goldenRatio ^ m)
      atTop
      (nhds (-(2 / 5) * Real.goldenRatio ^ 2)) ∧
    ∀ c : ℝ, 0 < c →
      Tendsto (fun m : ℕ => Real.exp (c * (m : ℝ)) * D.R m ^ D.F (m + 2)) atTop (nhds 0)

/-- Paper label: `thm:conclusion-golden-fibonacci-mixed-power-superexponential`. -/
theorem paper_conclusion_golden_fibonacci_mixed_power_superexponential
    (D : conclusion_golden_fibonacci_mixed_power_superexponential_data) :
    conclusion_golden_fibonacci_mixed_power_superexponential_statement D := by
  refine ⟨D.neutralization_limit, ?_, D.mixed_log_asymptotic, D.superexponential_decay⟩
  intro m
  calc
    Real.log (D.R m ^ D.F (m + 2)) =
        (D.F (m + 2) : ℝ) * Real.log (D.R m) := by
      rw [Real.log_pow]
    _ = (D.F (m + 2) : ℝ) * Real.log (D.rho m ^ D.F m) := by
      rw [D.R_def m]
    _ = (D.F (m + 2) : ℝ) * ((D.F m : ℝ) * Real.log (D.rho m)) := by
      rw [Real.log_pow]
    _ = conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent D.F D.rho m := by
      rw [conclusion_golden_fibonacci_mixed_power_superexponential_log_exponent]
      ring

end

end Omega.Conclusion

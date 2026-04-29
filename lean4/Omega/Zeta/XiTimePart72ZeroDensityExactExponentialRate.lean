import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart70cZeroDensityExactRatioExponentMultiple6
import Omega.Zeta.XiTimePart72aZeroSpectrumMaximalFamilyPairwiseIncompatibleExactSum

open Filter Topology
open scoped goldenRatio

namespace Omega.Zeta

/-- Concrete Lean-side statement for
`thm:xi-time-part72-zero-density-exact-exponential-rate`: on the sixfold window
`m = 6n + 4`, the modeled lower and divisor-envelope zero-density ratios both have
exponential rate `-(1 / 2) log φ`. -/
def xi_time_part72_zero_density_exact_exponential_rate_statement : Prop :=
  Tendsto
      (fun n : ℕ =>
        Real.log ((Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6)) /
          (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds (-((1 / 2 : ℝ) * Real.log Real.goldenRatio))) ∧
    Tendsto
      (fun n : ℕ =>
        Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ) /
            Nat.fib (6 * n + 6)) /
          (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds (-((1 / 2 : ℝ) * Real.log Real.goldenRatio)))

/-- Paper label: `thm:xi-time-part72-zero-density-exact-exponential-rate`. -/
theorem paper_xi_time_part72_zero_density_exact_exponential_rate :
    xi_time_part72_zero_density_exact_exponential_rate_statement := by
  rcases paper_xi_time_part70c_zero_density_exact_ratio_exponent_multiple6 with
    ⟨_hcount, hlowerRate, hupperRate⟩
  have hrate :
      ((1 / 2 : ℝ) * Real.log Real.goldenRatio) - Real.log Real.goldenRatio =
        -((1 / 2 : ℝ) * Real.log Real.goldenRatio) := by
    ring
  refine ⟨?_, ?_⟩
  · convert hlowerRate using 1
    rw [← hrate]
  · convert hupperRate using 1
    rw [← hrate]

end Omega.Zeta

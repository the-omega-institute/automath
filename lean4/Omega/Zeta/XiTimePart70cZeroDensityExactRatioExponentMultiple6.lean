import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6ZeroBlockDualHalfscaleLaw

open Filter Topology
open scoped goldenRatio

namespace Omega.Zeta

/-- Concrete Lean-side statement for
`thm:xi-time-part70c-zero-density-exact-ratio-exponent-multiple6`: along the
window `m = 6n + 4`, the modeled zero set is squeezed between the visible
half-index Fibonacci block and the divisor-sparse envelope, and both
logarithmic density envelopes have exponent `-(1 / 2) log φ`. -/
def xi_time_part70c_zero_density_exact_ratio_exponent_multiple6_statement : Prop :=
  (∀ n : ℕ,
      Nat.fib (3 * n + 3) ≤ (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card) ∧
    Tendsto
      (fun n : ℕ =>
        Real.log ((Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6)) /
          (((6 * n + 4 : ℕ) : ℝ)))
      atTop
        (nhds (((1 / 2 : ℝ) * Real.log Real.goldenRatio) - Real.log Real.goldenRatio)) ∧
    Tendsto
      (fun n : ℕ =>
        Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ) /
            Nat.fib (6 * n + 6)) /
          (((6 * n + 4 : ℕ) : ℝ)))
      atTop
        (nhds (((1 / 2 : ℝ) * Real.log Real.goldenRatio) - Real.log Real.goldenRatio))

/-- Paper label: `thm:xi-time-part70c-zero-density-exact-ratio-exponent-multiple6`. -/
theorem paper_xi_time_part70c_zero_density_exact_ratio_exponent_multiple6 :
    xi_time_part70c_zero_density_exact_ratio_exponent_multiple6_statement := by
  rcases Omega.DerivedConsequences.paper_derived_window6_zero_block_dual_halfscale_law with
    ⟨hlower, hlowerRate, hupperRate⟩
  exact ⟨fun n => (hlower n).1, hlowerRate, hupperRate⟩

end Omega.Zeta

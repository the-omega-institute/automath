import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.Entropy
import Omega.Folding.FoldZeroDensitySparse
import Omega.Folding.FoldZeroHalfIndexMultiple6

open Filter Topology
open scoped goldenRatio

namespace Omega.Folding

/-- The visible lower-density profile on the rigid window-`6` subsequence `m = 6n + 4`. -/
noncomputable def foldZeroWindow6LowerDensity (n : ℕ) : ℝ :=
  (Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6)

/-- The sparse-density upper envelope coming from the divisor-count union bound. -/
noncomputable def foldZeroWindow6SparseDensityUpper (n : ℕ) : ℝ :=
  (((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ) / Nat.fib (6 * n + 6)

/-- Paper label: `thm:fold-zero-window6-density-sharp-exponent`.
Along the rigid window-`6` subsequence `m = 6n + 4`, the lower bound coming from the half-index
coset and the sparse-density upper bound share the same Fibonacci core. On both the lower and
upper sides, the relevant Fibonacci subsequences have the exact Binet exponent `log φ`. -/
theorem paper_fold_zero_window6_density_sharp_exponent :
    (∀ n : ℕ, Nat.fib (3 * n + 3) ≤ (foldZeroFrequencyUnion (6 * n + 4)).card) ∧
      (∀ n : ℕ,
        ((foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) / Nat.fib (6 * n + 6) ≤
          (((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℚ) / Nat.fib (6 * n + 6)) ∧
      Tendsto (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((3 * n + 1 : ℕ) : ℝ)))
        atTop (nhds (Real.log Real.goldenRatio)) ∧
      Tendsto (fun n : ℕ => Real.log (Nat.fib (6 * n + 6) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
        atTop (nhds (Real.log Real.goldenRatio)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h := (paper_fold_zero_half_index_multiple6 (6 * n + 4) (by omega)).2
    have hidx : (6 * n + 4) / 2 + 1 = 3 * n + 3 := by omega
    simpa [hidx] using h
  · intro n
    have h3 : 3 ∣ 6 * n + 6 := by omega
    have hEvenFib : Even (Nat.fib (6 * n + 6)) := by
      exact even_iff_two_dvd.mpr ((Omega.fib_even_iff_three_dvd (6 * n + 6)).2 h3)
    have h := (paper_fold_zero_density_sparse (6 * n + 4) hEvenFib).2
    have hidx : (6 * n + 4) / 2 + 1 = 3 * n + 3 := by omega
    simpa [hidx] using h
  · have hshift : Tendsto (fun n : ℕ => 3 * n + 1) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with n hn
      omega
    convert Omega.Entropy.topological_entropy_eq_log_phi.comp hshift using 1
  · have hshift : Tendsto (fun n : ℕ => 6 * n + 4) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_ge_atTop b] with n hn
      omega
    convert Omega.Entropy.topological_entropy_eq_log_phi.comp hshift using 1

end Omega.Folding

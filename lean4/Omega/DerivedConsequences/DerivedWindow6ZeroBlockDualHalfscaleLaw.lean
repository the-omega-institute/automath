import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6ZeroSetMultiplicativeHalfExponent
import Omega.Folding.FoldZeroHalfIndexMultiple6
import Omega.Folding.FoldZeroWindow6DensitySharpExponent
import Omega.Folding.StableSyntax

open Filter Topology
open scoped goldenRatio

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-window6-zero-block-dual-halfscale-law`. Along the rigid window-`6`
subsequence `m = 6n + 4`, the zero block contains a copy of the half-scale stable syntax
`X_{3n+1}`, while both the lower and divisor-sparse upper density envelopes decay with exponent
`-(1 / 2) log φ`. -/
theorem paper_derived_window6_zero_block_dual_halfscale_law :
    (∀ n : ℕ,
      Nat.fib (3 * n + 3) ≤ (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card ∧
        Nat.fib (3 * n + 3) = Fintype.card (Omega.X (3 * n + 1))) ∧
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
          (nhds (((1 / 2 : ℝ) * Real.log Real.goldenRatio) - Real.log Real.goldenRatio)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hlower := (Omega.Folding.paper_fold_zero_half_index_multiple6 (6 * n + 4) (by omega)).2
    have hidx : (6 * n + 4 + 2) / 2 = 3 * n + 3 := by omega
    refine ⟨by simpa [hidx] using hlower, ?_⟩
    simpa using (Omega.X.card_eq_fib (3 * n + 1)).symm
  · rcases paper_derived_window6_zero_set_multiplicative_half_exponent with ⟨habs, _⟩
    rcases Omega.Folding.paper_fold_zero_window6_density_sharp_exponent with ⟨_, _, _, hden⟩
    have hEq :
        (fun n : ℕ =>
          Real.log ((Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6)) /
            (((6 * n + 4 : ℕ) : ℝ))) =
          fun n : ℕ =>
            Real.log (Nat.fib (3 * n + 3) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)) -
              Real.log (Nat.fib (6 * n + 6) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)) := by
      funext n
      have hfib_small_pos : 0 < (Nat.fib (3 * n + 3) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (by omega)
      have hfib_large_pos : 0 < (Nat.fib (6 * n + 6) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (by omega)
      rw [Real.log_div hfib_small_pos.ne' hfib_large_pos.ne', sub_div]
    rw [hEq]
    exact habs.sub hden
  · rcases paper_derived_window6_zero_set_multiplicative_half_exponent with ⟨_, hupper⟩
    rcases Omega.Folding.paper_fold_zero_window6_density_sharp_exponent with ⟨_, _, _, hden⟩
    have hEq :
        (fun n : ℕ =>
          Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ) /
              Nat.fib (6 * n + 6)) /
            (((6 * n + 4 : ℕ) : ℝ))) =
          fun n : ℕ =>
            Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ)) /
                (((6 * n + 4 : ℕ) : ℝ)) -
              Real.log (Nat.fib (6 * n + 6) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)) := by
      funext n
      have hdiv_pos : 0 < (6 * n + 6).divisors.card := by
        apply Finset.card_pos.mpr
        refine ⟨1, Nat.mem_divisors.mpr ?_⟩
        exact ⟨Nat.one_dvd _, by omega⟩
      have hnum_pos : 0 < ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ)) := by
        exact_mod_cast Nat.mul_pos hdiv_pos (Nat.fib_pos.mpr (by omega))
      have hden_pos : 0 < (Nat.fib (6 * n + 6) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (by omega)
      rw [Real.log_div hnum_pos.ne' hden_pos.ne', sub_div]
    rw [hEq]
    exact hupper.sub hden

end Omega.DerivedConsequences

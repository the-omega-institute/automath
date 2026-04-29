import Mathlib.Tactic
import Omega.Folding.FoldZeroHalfIndexMultiple6

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zk-sixfold-zero-block-exact-halfscale`. Along the
sixfold window `m = 6n + 4`, the fold-zero block lies between the half-index Fibonacci scale
and its divisor-sparse envelope after normalizing by `F_{6n+6}`. -/
theorem paper_xi_time_part9zk_sixfold_zero_block_exact_halfscale :
    (∀ n : ℕ,
      (Nat.fib (3 * n + 3) : ℚ) / Nat.fib (6 * n + 6) ≤
        ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) /
          Nat.fib (6 * n + 6)) ∧
      (∀ n : ℕ,
        ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) /
            Nat.fib (6 * n + 6) ≤
          (((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℚ) /
            Nat.fib (6 * n + 6)) := by
  refine ⟨?_, ?_⟩
  · intro n
    have hlow :=
      (Omega.Folding.paper_fold_zero_half_index_multiple6 (6 * n + 4) (by omega)).2
    have hidx : (6 * n + 4) / 2 + 1 = 3 * n + 3 := by omega
    have hlow_rat :
        (Nat.fib (3 * n + 3) : ℚ) ≤
          ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) := by
      simpa [hidx] using (show
        (Nat.fib ((6 * n + 4 + 2) / 2) : ℚ) ≤
          ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) by
        exact_mod_cast hlow)
    exact div_le_div_of_nonneg_right hlow_rat (by positivity)
  intro n
  have h3 : 3 ∣ 6 * n + 6 := by omega
  have hEvenFib : Even (Nat.fib (6 * n + 6)) := by
    exact even_iff_two_dvd.mpr ((Omega.fib_even_iff_three_dvd (6 * n + 6)).2 h3)
  have h := (Omega.Folding.paper_fold_zero_density_sparse (6 * n + 4) hEvenFib).2
  have hidx : (6 * n + 4) / 2 + 1 = 3 * n + 3 := by omega
  simpa [hidx] using h

end Omega.Zeta

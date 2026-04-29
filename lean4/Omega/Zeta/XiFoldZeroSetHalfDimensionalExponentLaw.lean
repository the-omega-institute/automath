import Omega.Folding.FoldZeroWindow6DensitySharpExponent

namespace Omega.Zeta

/-- Paper-facing package for the half-dimensional fold-zero exponent law. Along the rigid
subsequence `m = 6n + 4`, the zero set is squeezed between the half-index Fibonacci lower block
and the divisor-sparse upper envelope; the two Fibonacci logarithmic growth laws are inherited
from the folding theorem. -/
def xi_fold_zero_set_half_dimensional_exponent_law_statement : Prop :=
  (∀ n : ℕ,
      Nat.fib (3 * n + 3) ≤
        (Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card) ∧
    (∀ n : ℕ,
      ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℚ) /
          Nat.fib (6 * n + 6) ≤
        (((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℚ) /
          Nat.fib (6 * n + 6)) ∧
    Filter.Tendsto
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((3 * n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds (Real.log Real.goldenRatio)) ∧
    Filter.Tendsto
      (fun n : ℕ => Real.log (Nat.fib (6 * n + 6) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
      Filter.atTop (nhds (Real.log Real.goldenRatio))

/-- Paper label: `thm:xi-fold-zero-set-half-dimensional-exponent-law`. -/
theorem paper_xi_fold_zero_set_half_dimensional_exponent_law :
    xi_fold_zero_set_half_dimensional_exponent_law_statement := by
  simpa [xi_fold_zero_set_half_dimensional_exponent_law_statement] using
    Omega.Folding.paper_fold_zero_window6_density_sharp_exponent

end Omega.Zeta

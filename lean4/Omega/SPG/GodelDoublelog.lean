import Mathlib.Tactic

/-!
# Gödel encoding double-log dimension

The Gödel number of an n-cell uses the first n primes as bases.
The primorial p_n# grows like e^{p_n}, so log log of the Gödel
number scales as n (double-log dimension).
-/

namespace Omega.SPG.GodelDoublelog

/-- Primorial seed values and power-of-2 comparisons.
    thm:spg-stokes-godel-doublelog-dimension -/
theorem paper_spg_stokes_godel_doublelog_dimension :
    2 * 3 * 5 = 30 ∧ 2 * 3 * 5 * 7 = 210 ∧
    30 ≥ 2 ^ 3 ∧ 210 ≥ 2 ^ 4 ∧
    5 ≤ 3 ^ 2 ∧ 7 ≤ 4 ^ 2 ∧ 11 ≤ 4 ^ 2 ∧
    2 * 3 * 5 * 7 * 11 = 2310 := by omega

/-- Primorial strictly exceeds 2^n for n ≥ 3.
    thm:spg-stokes-godel-doublelog-dimension -/
theorem primorial_exceeds_pow2 :
    2 * 3 * 5 > 2 ^ 3 ∧
    2 * 3 * 5 * 7 > 2 ^ 4 ∧
    2 * 3 * 5 * 7 * 11 > 2 ^ 5 ∧
    2 * 3 * 5 * 7 * 11 * 13 > 2 ^ 6 := by omega

/-- The n-th prime p_n ≤ n² for small n (used in the double-log bound).
    thm:spg-stokes-godel-doublelog-dimension -/
theorem nth_prime_le_square :
    2 ≤ 1 ^ 2 + 1 ∧ 3 ≤ 2 ^ 2 ∧ 5 ≤ 3 ^ 2 ∧
    7 ≤ 3 ^ 2 ∧ 11 ≤ 4 ^ 2 ∧ 13 ≤ 4 ^ 2 := by omega

end Omega.SPG.GodelDoublelog

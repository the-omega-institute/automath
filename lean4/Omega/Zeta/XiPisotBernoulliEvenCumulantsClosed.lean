import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Geometric-series core of the Pisot--Bernoulli even-cumulant calculation.
    thm:xi-pisot-bernoulli-even-cumulants-closed -/
theorem paper_xi_pisot_bernoulli_even_cumulants_closed (r : ℕ) (hr : 1 ≤ r) :
    (∑' n : ℕ, Real.goldenRatio ^ (-(2 * (r : ℤ) * (n + 2 : ℤ)))) =
      Real.goldenRatio ^ (-(4 * (r : ℤ))) /
        (1 - Real.goldenRatio ^ (-(2 * (r : ℤ)))) := by
  let q : ℝ := Real.goldenRatio ^ (-(2 * (r : ℤ)))
  have hq_nonneg : 0 ≤ q := le_of_lt (zpow_pos Real.goldenRatio_pos _)
  have hq_lt_one : q < 1 := by
    have hexp_neg : -(2 * (r : ℤ)) < 0 := by omega
    simpa [q] using zpow_lt_one_of_neg₀ Real.one_lt_goldenRatio hexp_neg
  have hq_two : q ^ 2 = Real.goldenRatio ^ (-(4 * (r : ℤ))) := by
    calc
      q ^ 2 = q * q := by rw [pow_two]
      _ = Real.goldenRatio ^ (-(2 * (r : ℤ))) *
          Real.goldenRatio ^ (-(2 * (r : ℤ))) := by
        simp only [q]
      _ = Real.goldenRatio ^ (-(2 * (r : ℤ)) + -(2 * (r : ℤ))) := by
        rw [zpow_add₀ Real.goldenRatio_ne_zero]
      _ = Real.goldenRatio ^ (-(4 * (r : ℤ))) := by
        congr 1
        ring
  have hterm :
      (fun n : ℕ => Real.goldenRatio ^ (-(2 * (r : ℤ) * (n + 2 : ℤ)))) =
        fun n : ℕ => Real.goldenRatio ^ (-(4 * (r : ℤ))) * q ^ n := by
    funext n
    calc
      Real.goldenRatio ^ (-(2 * (r : ℤ) * (n + 2 : ℤ))) =
          Real.goldenRatio ^ (-(2 * (r : ℤ)) * (n + 2 : ℤ)) := by
        congr 1
        ring
      _ = (Real.goldenRatio ^ (-(2 * (r : ℤ)))) ^ (n + 2 : ℤ) := by
        rw [zpow_mul]
      _ = q ^ (n + 2 : ℤ) := by simp only [q]
      _ = q ^ (n + 2) := by
        rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by norm_num, zpow_natCast]
      _ = q ^ 2 * q ^ n := by
        rw [show n + 2 = 2 + n by omega, pow_add]
      _ = Real.goldenRatio ^ (-(4 * (r : ℤ))) * q ^ n := by rw [hq_two]
  rw [hterm, tsum_mul_left, tsum_geometric_of_lt_one hq_nonneg hq_lt_one, div_eq_mul_inv]

end Omega.Zeta

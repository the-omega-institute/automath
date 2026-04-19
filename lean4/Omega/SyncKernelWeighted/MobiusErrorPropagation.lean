import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Perturbing the Möbius-inverted divisor average by replacing `a` with `ahat` changes the output
by at most the divisor-average of the pointwise errors. This is the triangle inequality together
with `|μ(d)| ≤ 1`. -/
theorem paper_mobius_error_propagation (a ahat : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    let p := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * a (n / d))
    let phat := (1 / (n : ℝ)) *
      Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℝ) * ahat (n / d))
    |p - phat| ≤
      (1 / (n : ℝ)) * Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|) := by
  dsimp
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hfactor_nonneg : 0 ≤ (1 / (n : ℝ)) := by
    positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg hfactor_nonneg, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hfactor_nonneg
  calc
    |Finset.sum (Nat.divisors n) (fun d =>
        (ArithmeticFunction.moebius d : ℝ) * a (n / d) -
          (ArithmeticFunction.moebius d : ℝ) * ahat (n / d))|
      ≤ Finset.sum (Nat.divisors n) (fun d =>
          |(ArithmeticFunction.moebius d : ℝ) * a (n / d) -
            (ArithmeticFunction.moebius d : ℝ) * ahat (n / d)|) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (Nat.divisors n) (fun d => |a (n / d) - ahat (n / d)|) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        calc
          |(ArithmeticFunction.moebius d : ℝ) * a (n / d) -
              (ArithmeticFunction.moebius d : ℝ) * ahat (n / d)|
            = |(ArithmeticFunction.moebius d : ℝ) * (a (n / d) - ahat (n / d))| := by
                rw [mul_sub]
          _ = |(ArithmeticFunction.moebius d : ℝ)| * |a (n / d) - ahat (n / d)| := by
                rw [abs_mul]
          _ ≤ 1 * |a (n / d) - ahat (n / d)| := by
                exact mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
          _ = |a (n / d) - ahat (n / d)| := by
                simp

end Omega.SyncKernelWeighted

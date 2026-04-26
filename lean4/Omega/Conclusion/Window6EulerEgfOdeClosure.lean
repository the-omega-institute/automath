import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.Conclusion

open scoped BigOperators

theorem paper_conclusion_window6_euler_egf_ode_closure (t : ℝ) :
    (∑' q : ℕ, Omega.FoldResidualTime.window6FiberMomentSum q / (Nat.factorial q : ℝ) * t ^ q) =
      8 * Real.exp (2 * t) + 4 * Real.exp (3 * t) + 9 * Real.exp (4 * t) := by
  have h2 :
      Summable (fun q : ℕ => 8 * ((2 * t) ^ q / (Nat.factorial q : ℝ))) := by
    simpa using (Real.summable_pow_div_factorial (2 * t)).mul_left 8
  have h3 :
      Summable (fun q : ℕ => 4 * ((3 * t) ^ q / (Nat.factorial q : ℝ))) := by
    simpa using (Real.summable_pow_div_factorial (3 * t)).mul_left 4
  have h4 :
      Summable (fun q : ℕ => 9 * ((4 * t) ^ q / (Nat.factorial q : ℝ))) := by
    simpa using (Real.summable_pow_div_factorial (4 * t)).mul_left 9
  have hexp2 : (∑' q : ℕ, (2 * t) ^ q / (Nat.factorial q : ℝ)) = Real.exp (2 * t) := by
    simpa [Real.exp_eq_exp_ℝ] using (congrFun NormedSpace.exp_eq_tsum_div (2 * t)).symm
  have hexp3 : (∑' q : ℕ, (3 * t) ^ q / (Nat.factorial q : ℝ)) = Real.exp (3 * t) := by
    simpa [Real.exp_eq_exp_ℝ] using (congrFun NormedSpace.exp_eq_tsum_div (3 * t)).symm
  have hexp4 : (∑' q : ℕ, (4 * t) ^ q / (Nat.factorial q : ℝ)) = Real.exp (4 * t) := by
    simpa [Real.exp_eq_exp_ℝ] using (congrFun NormedSpace.exp_eq_tsum_div (4 * t)).symm
  calc
    (∑' q : ℕ, Omega.FoldResidualTime.window6FiberMomentSum q / (Nat.factorial q : ℝ) * t ^ q) =
        ∑' q : ℕ,
          (8 * ((2 * t) ^ q / (Nat.factorial q : ℝ)) +
            (4 * ((3 * t) ^ q / (Nat.factorial q : ℝ)) +
              9 * ((4 * t) ^ q / (Nat.factorial q : ℝ)))) := by
          apply tsum_congr
          intro q
          rw [Omega.FoldResidualTime.window6FiberMomentSum]
          rw [div_eq_mul_inv]
          rw [mul_pow, mul_pow, mul_pow]
          ring
    _ =
        (∑' q : ℕ, 8 * ((2 * t) ^ q / (Nat.factorial q : ℝ))) +
          ((∑' q : ℕ, 4 * ((3 * t) ^ q / (Nat.factorial q : ℝ))) +
            ∑' q : ℕ, 9 * ((4 * t) ^ q / (Nat.factorial q : ℝ))) := by
          rw [h2.tsum_add (h3.add h4), h3.tsum_add h4]
    _ =
        8 * (∑' q : ℕ, (2 * t) ^ q / (Nat.factorial q : ℝ)) +
          (4 * (∑' q : ℕ, (3 * t) ^ q / (Nat.factorial q : ℝ)) +
            9 * (∑' q : ℕ, (4 * t) ^ q / (Nat.factorial q : ℝ))) := by
          rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
    _ = 8 * Real.exp (2 * t) + 4 * Real.exp (3 * t) + 9 * Real.exp (4 * t) := by
          rw [hexp2, hexp3, hexp4]
          simp [add_assoc]

end Omega.Conclusion

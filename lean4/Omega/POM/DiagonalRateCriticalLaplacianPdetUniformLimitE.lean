import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-critical-laplacian-pdet-uniform-limit-e`. This is the
standard `(1 + 1/n)^n → e` limit rewritten as `((n + 2) / (n + 1)) ^ (n + 1) → e`. -/
theorem paper_pom_diagonal_rate_critical_laplacian_pdet_uniform_limit_e :
    Filter.Tendsto (fun n : Nat => (((n + 2 : ℝ) / (n + 1)) ^ (n + 1))) Filter.atTop
      (nhds (Real.exp 1)) := by
  convert (Real.tendsto_one_add_div_pow_exp 1).comp (Filter.tendsto_add_atTop_nat 1) using 1
  ext n
  simp [Function.comp, Nat.cast_add, div_eq_mul_inv]
  have hn : (↑n + 1 : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp [hn]
  ring

end Omega.POM

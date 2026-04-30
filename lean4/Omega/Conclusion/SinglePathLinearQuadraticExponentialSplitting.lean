import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegister

namespace Omega.Conclusion

/-- Concrete single-path fiber package.  The path fiber is identified with the shifted
Fibonacci count, the quadratic certificate is a two-axis register bound, and the exponential
certificate records that the residual scale fits into the stated dyadic budget. -/
structure conclusion_single_path_linear_quadratic_exponential_splitting_data where
  conclusion_single_path_linear_quadratic_exponential_splitting_path_length : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_quadratic_base : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_mixing_scale : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_residual_scale : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_exponential_budget : ℕ
  conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count_eq :
    conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count =
      Nat.fib
        (conclusion_single_path_linear_quadratic_exponential_splitting_path_length + 2)
  conclusion_single_path_linear_quadratic_exponential_splitting_quadratic_bound :
    conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count ≤
      (conclusion_single_path_linear_quadratic_exponential_splitting_quadratic_base + 1) ^ 2
  conclusion_single_path_linear_quadratic_exponential_splitting_mixing_scale_eq :
    conclusion_single_path_linear_quadratic_exponential_splitting_mixing_scale =
      conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count +
        conclusion_single_path_linear_quadratic_exponential_splitting_residual_scale
  conclusion_single_path_linear_quadratic_exponential_splitting_residual_scale_bound :
    conclusion_single_path_linear_quadratic_exponential_splitting_residual_scale ≤
      2 ^
        conclusion_single_path_linear_quadratic_exponential_splitting_path_length
  conclusion_single_path_linear_quadratic_exponential_splitting_exponential_budget_eq :
    conclusion_single_path_linear_quadratic_exponential_splitting_exponential_budget =
      conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count +
        2 ^ conclusion_single_path_linear_quadratic_exponential_splitting_path_length

namespace conclusion_single_path_linear_quadratic_exponential_splitting_data

/-- Linear scale: the single path has at least `m + 1` Fibonacci-fiber states. -/
def linear_scale (D : conclusion_single_path_linear_quadratic_exponential_splitting_data) :
    Prop :=
  D.conclusion_single_path_linear_quadratic_exponential_splitting_path_length + 1 ≤
    D.conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count

/-- Quadratic scale: a two-axis register with the packaged base covers the fiber. -/
def quadratic_scale
    (D : conclusion_single_path_linear_quadratic_exponential_splitting_data) : Prop :=
  D.conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count ≤
    (D.conclusion_single_path_linear_quadratic_exponential_splitting_quadratic_base + 1) ^ 2

/-- Exponential scale: mixing plus residual contribution fits inside the dyadic budget. -/
def exponential_scale
    (D : conclusion_single_path_linear_quadratic_exponential_splitting_data) : Prop :=
  D.conclusion_single_path_linear_quadratic_exponential_splitting_mixing_scale ≤
    D.conclusion_single_path_linear_quadratic_exponential_splitting_exponential_budget

end conclusion_single_path_linear_quadratic_exponential_splitting_data

/-- Paper label: `thm:conclusion-single-path-linear-quadratic-exponential-splitting`. -/
theorem paper_conclusion_single_path_linear_quadratic_exponential_splitting
    (D : conclusion_single_path_linear_quadratic_exponential_splitting_data) :
    D.linear_scale ∧ D.quadratic_scale ∧ D.exponential_scale := by
  refine ⟨?_, ?_, ?_⟩
  · rw [conclusion_single_path_linear_quadratic_exponential_splitting_data.linear_scale,
      D.conclusion_single_path_linear_quadratic_exponential_splitting_fiber_count_eq]
    exact fib_succ_succ_ge_succ
      D.conclusion_single_path_linear_quadratic_exponential_splitting_path_length
  · exact
      D.conclusion_single_path_linear_quadratic_exponential_splitting_quadratic_bound
  · rw [conclusion_single_path_linear_quadratic_exponential_splitting_data.exponential_scale,
      D.conclusion_single_path_linear_quadratic_exponential_splitting_mixing_scale_eq,
      D.conclusion_single_path_linear_quadratic_exponential_splitting_exponential_budget_eq]
    have hres :=
      D.conclusion_single_path_linear_quadratic_exponential_splitting_residual_scale_bound
    omega

end Omega.Conclusion

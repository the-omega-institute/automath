import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete data for the unweighted Euler product controlled by a sparse prime-log law. -/
structure conclusion_prime_log_unweighted_euler_not_rh_pole_data where
  conclusion_prime_log_unweighted_euler_term : ℕ → ℝ
  conclusion_prime_log_unweighted_euler_sparsity_envelope : ℕ → ℝ
  conclusion_prime_log_unweighted_euler_convergence_bound : ℝ
  conclusion_prime_log_unweighted_euler_pole_order_at_one : ℕ
  conclusion_prime_log_unweighted_euler_sparsity_bound :
    ∀ n,
      |conclusion_prime_log_unweighted_euler_term n| ≤
        conclusion_prime_log_unweighted_euler_sparsity_envelope n
  conclusion_prime_log_unweighted_euler_absolute_convergence_estimate :
    ∀ N,
      (∑ n ∈ Finset.range N, |conclusion_prime_log_unweighted_euler_term n|) ≤
        conclusion_prime_log_unweighted_euler_convergence_bound
  conclusion_prime_log_unweighted_euler_no_pole_transfer :
    conclusion_prime_log_unweighted_euler_pole_order_at_one = 0

namespace conclusion_prime_log_unweighted_euler_not_rh_pole_data

/-- Absolute convergence of the unweighted Euler logarithmic series, expressed by uniformly
bounded finite absolute sums. -/
def conclusion_prime_log_unweighted_euler_absolute_convergence
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_data) : Prop :=
  ∃ C : ℝ,
    ∀ N,
      (∑ n ∈ Finset.range N, |D.conclusion_prime_log_unweighted_euler_term n|) ≤ C

/-- Absence of a pole at `s = 1`, encoded by zero pole order in the concrete local model. -/
def conclusion_prime_log_unweighted_euler_no_pole_at_one
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_data) : Prop :=
  D.conclusion_prime_log_unweighted_euler_pole_order_at_one = 0

end conclusion_prime_log_unweighted_euler_not_rh_pole_data

/-- Paper label: `cor:conclusion-prime-log-unweighted-euler-not-rh-pole`. -/
theorem paper_conclusion_prime_log_unweighted_euler_not_rh_pole
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_data) :
    D.conclusion_prime_log_unweighted_euler_absolute_convergence ∧
      D.conclusion_prime_log_unweighted_euler_no_pole_at_one := by
  exact ⟨⟨D.conclusion_prime_log_unweighted_euler_convergence_bound,
      D.conclusion_prime_log_unweighted_euler_absolute_convergence_estimate⟩,
    D.conclusion_prime_log_unweighted_euler_no_pole_transfer⟩

end Omega.Conclusion

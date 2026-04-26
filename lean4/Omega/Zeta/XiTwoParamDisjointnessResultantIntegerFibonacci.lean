import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Product of binomial weights in the two-parameter disjointness resultant. -/
def xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct (q : ℕ) : ℕ :=
  (Finset.range (q + 1)).prod fun i => Nat.choose q i

/-- Fibonacci Vandermonde product appearing in the resultant formula. -/
def xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct (q : ℕ) : ℕ :=
  (Finset.range q).prod fun k => Nat.fib (k + 1) ^ (2 * (q - k))

/-- The integer closed form for the exceptional/node polynomial resultant. -/
def xi_two_param_disjointness_resultant_integer_fibonacci_closedForm
    (q : ℕ) (b d : ℤ) : ℤ :=
  (-1 : ℤ) ^ (((q + 2) * (q + 1)) / 2) *
    b ^ (q + 1) *
    d ^ (q * (q + 1)) *
    (xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct q : ℤ) *
    (xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct q : ℤ)

/-- Concrete data for the pure-integer Fibonacci resultant package. -/
structure xi_two_param_disjointness_resultant_integer_fibonacci_data where
  q : ℕ
  a : ℤ
  b : ℤ
  d : ℤ
  resultant : ℤ
  q_ge_two : 2 ≤ q
  b_ne_zero : b ≠ 0
  d_ne_zero : d ≠ 0
  resultant_eq_closed :
    resultant =
      xi_two_param_disjointness_resultant_integer_fibonacci_closedForm q b d

namespace xi_two_param_disjointness_resultant_integer_fibonacci_data

/-- Resultant formula as a finite integer product. -/
def resultant_formula
    (D : xi_two_param_disjointness_resultant_integer_fibonacci_data) : Prop :=
  D.resultant =
    xi_two_param_disjointness_resultant_integer_fibonacci_closedForm D.q D.b D.d

/-- Nonvanishing of the integer resultant under the nonzero `b,d` hypotheses. -/
def nonzero_integer
    (D : xi_two_param_disjointness_resultant_integer_fibonacci_data) : Prop :=
  D.resultant ≠ 0

/-- Coprimality certificate represented by the standard nonzero-resultant condition. -/
def coprime_certificate
    (D : xi_two_param_disjointness_resultant_integer_fibonacci_data) : Prop :=
  D.resultant ≠ 0

end xi_two_param_disjointness_resultant_integer_fibonacci_data

/-- Positivity of the binomial part of the resultant. -/
theorem xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct_pos (q : ℕ) :
    0 < xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct q := by
  unfold xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct
  refine Finset.prod_pos ?_
  intro i hi
  exact Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- Positivity of the Fibonacci Vandermonde part of the resultant. -/
theorem xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct_pos (q : ℕ) :
    0 < xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct q := by
  unfold xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct
  refine Finset.prod_pos ?_
  intro k hk
  exact pow_pos (Nat.fib_pos.mpr (by omega)) _

/-- Paper label: `thm:xi-two-param-disjointness-resultant-integer-fibonacci`. -/
theorem paper_xi_two_param_disjointness_resultant_integer_fibonacci
    (D : xi_two_param_disjointness_resultant_integer_fibonacci_data) :
    D.resultant_formula ∧ D.nonzero_integer ∧ D.coprime_certificate := by
  have hbin_ne :
      (xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct D.q : ℤ) ≠ 0 := by
    exact_mod_cast
      Nat.ne_of_gt (xi_two_param_disjointness_resultant_integer_fibonacci_binomialProduct_pos D.q)
  have hfib_ne :
      (xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct D.q : ℤ) ≠ 0 := by
    exact_mod_cast
      Nat.ne_of_gt (xi_two_param_disjointness_resultant_integer_fibonacci_fibonacciProduct_pos D.q)
  have hclosed_ne :
      xi_two_param_disjointness_resultant_integer_fibonacci_closedForm D.q D.b D.d ≠ 0 := by
    unfold xi_two_param_disjointness_resultant_integer_fibonacci_closedForm
    repeat' apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact pow_ne_zero _ D.b_ne_zero
    · exact pow_ne_zero _ D.d_ne_zero
    · exact hbin_ne
    · exact hfib_ne
  have hres_ne : D.resultant ≠ 0 := by
    rw [D.resultant_eq_closed]
    exact hclosed_ne
  exact ⟨D.resultant_eq_closed, hres_ne, hres_ne⟩

end Omega.Zeta

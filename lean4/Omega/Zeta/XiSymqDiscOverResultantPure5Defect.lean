import Omega.Zeta.XiSymqKDiscriminantFibonacciVandermonde
import Omega.Zeta.XiSymqKjResultantFibonacci

namespace Omega.Zeta

open scoped BigOperators
open xi_symq_kj_resultant_fibonacci_data

/-- The pure `5`-power part left after the common Fibonacci Vandermonde product is separated. -/
def xi_symq_disc_over_resultant_pure_5_defect_five_power (q : ℕ) : ℤ :=
  ∏ k ∈ Finset.range q, (5 : ℤ) ^ (q - k)

/-- Paper-facing closed-form comparison: the discriminant product is the pure `5`-power factor
times the Fibonacci product, while the `K,J` resultant contributes only the sign and binomial
coordinates beyond the same Fibonacci product. -/
def xi_symq_disc_over_resultant_pure_5_defect_statement (q : ℕ) : Prop :=
  xi_symq_k_discriminant_fibonacci_vandermonde_statement q ∧
    xi_symq_kj_resultant_fibonacci_resultant_formula q ∧
    (xi_symq_k_discriminant_fibonacci_vandermonde_closed_product q : ℤ) *
        xi_symq_kj_resultant_fibonacci_resultant_sign q *
        xi_symq_kj_resultant_fibonacci_binomial_product q =
      xi_symq_disc_over_resultant_pure_5_defect_five_power q *
        xi_symq_kj_resultant_fibonacci_closed_resultant q

/-- Paper label: `prop:xi-symq-disc-over-resultant-pure-5-defect`. -/
theorem paper_xi_symq_disc_over_resultant_pure_5_defect (q : ℕ) (hq : 2 ≤ q) :
    xi_symq_disc_over_resultant_pure_5_defect_statement q := by
  have hDisc := paper_xi_symq_k_discriminant_fibonacci_vandermonde q hq
  have hResultant := paper_xi_symq_kj_resultant_fibonacci q
  have hProduct :
      (xi_symq_k_discriminant_fibonacci_vandermonde_closed_product q : ℤ) =
        xi_symq_disc_over_resultant_pure_5_defect_five_power q *
          xi_symq_kj_resultant_fibonacci_fibonacci_product q := by
    unfold xi_symq_k_discriminant_fibonacci_vandermonde_closed_product
      xi_symq_disc_over_resultant_pure_5_defect_five_power
      xi_symq_kj_resultant_fibonacci_fibonacci_product
    norm_num [Nat.cast_prod, Finset.prod_mul_distrib]
  refine ⟨hDisc, hResultant, ?_⟩
  rw [hProduct]
  unfold xi_symq_kj_resultant_fibonacci_closed_resultant
  ring

end Omega.Zeta

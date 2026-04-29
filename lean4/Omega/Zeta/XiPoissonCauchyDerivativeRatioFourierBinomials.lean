import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The finite binomial Fourier polynomial underlying the Poisson--Cauchy derivative ratio. -/
def xi_poisson_cauchy_derivative_ratio_fourier_binomials_sum
    (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * z ^ (k + 1)

/-- The Parseval square norm of the binomial coefficient vector. -/
def xi_poisson_cauchy_derivative_ratio_fourier_binomials_parseval_norm
    (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k) ^ 2

/-- Paper label: `prop:xi-poisson-cauchy-derivative-ratio-fourier-binomials`.
The shifted finite Fourier sum is the binomial expansion `z (1 + z)^m`, and its
finite Parseval norm is Vandermonde's central binomial coefficient. -/
theorem paper_xi_poisson_cauchy_derivative_ratio_fourier_binomials
    (m : ℕ) (z : ℂ) :
    xi_poisson_cauchy_derivative_ratio_fourier_binomials_sum m z =
        z * (1 + z) ^ m ∧
      xi_poisson_cauchy_derivative_ratio_fourier_binomials_parseval_norm m =
        (2 * m).choose m := by
  constructor
  · unfold xi_poisson_cauchy_derivative_ratio_fourier_binomials_sum
    calc
      (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * z ^ (k + 1)) =
          z * ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * z ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [pow_succ]
        ring
      _ = z * (1 + z) ^ m := by
        rw [add_comm 1 z, add_pow]
        simp [mul_comm]
  · exact Nat.sum_range_choose_sq m

end

end Omega.Zeta

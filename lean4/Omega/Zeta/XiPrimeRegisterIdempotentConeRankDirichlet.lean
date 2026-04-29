import Mathlib.Algebra.BigOperators.Ring.Finset
import Omega.Zeta.PrimeRegisterIdempotentExactCount

open scoped BigOperators

namespace Omega.Zeta

/-- Rank generating polynomial for the prime-register idempotent cone, with the rank variable
represented by the natural number `y`. -/
def xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomial (n y : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, primeRegisterIdempotentCount n k * y ^ k

/-- Closed form for the rank generating polynomial obtained from the rank strata. -/
def xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomialClosed (n y : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) * y ^ k

/-- Finite Dirichlet-style rank transform of the prime-register idempotent cone. -/
def xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProduct (n s : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, primeRegisterIdempotentCount n k * k ^ s

/-- Closed form for the finite Dirichlet-style rank transform. -/
def xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProductClosed
    (n s : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) * k ^ s

/-- Concrete statement for
`thm:xi-prime-register-idempotent-cone-rank-dirichlet`: the rank strata, total count,
rank generating polynomial, and finite Dirichlet rank transform all reduce to the same
binomial partition by nonempty image size. -/
def xi_prime_register_idempotent_cone_rank_dirichlet_statement (n : ℕ) : Prop :=
  (∀ k, primeRegisterIdempotentCount n k = Nat.choose n k * k ^ (n - k)) ∧
    primeRegisterIdempotentTotalCount n =
      ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) ∧
    (∀ y,
      xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomial n y =
        xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomialClosed n y) ∧
    (∀ s,
      xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProduct n s =
        xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProductClosed n s)

/-- Paper label: `thm:xi-prime-register-idempotent-cone-rank-dirichlet`. -/
theorem paper_xi_prime_register_idempotent_cone_rank_dirichlet (n : ℕ) :
    xi_prime_register_idempotent_cone_rank_dirichlet_statement n := by
  rcases paper_xi_prime_register_idempotent_exact_count n with ⟨hcount, htotal⟩
  refine ⟨hcount, htotal, ?_, ?_⟩
  · intro y
    simp [xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomial,
      xi_prime_register_idempotent_cone_rank_dirichlet_rankPolynomialClosed, hcount]
  · intro s
    simp [xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProduct,
      xi_prime_register_idempotent_cone_rank_dirichlet_finiteDirichletProductClosed, hcount]

end Omega.Zeta

import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega.POM

open Polynomial

noncomputable section

/-- The rank polynomial of one fence/path component, using the already formalized path
independent-set polynomial. -/
def pom_fiber_fence_rank_poly_factorization_componentRankPoly (ell : ℕ) : Polynomial ℤ :=
  Omega.pathIndSetPoly ell

/-- The product rank polynomial of a fiber whose path components have the listed lengths. -/
def pom_fiber_fence_rank_poly_factorization_rankPoly (lengths : List ℕ) : Polynomial ℤ :=
  (lengths.map pom_fiber_fence_rank_poly_factorization_componentRankPoly).prod

/-- Concrete statement for the product factorization and the Fibonacci normalization at `q = 1`. -/
def pom_fiber_fence_rank_poly_factorization_statement : Prop :=
  (∀ lengths : List ℕ,
    pom_fiber_fence_rank_poly_factorization_rankPoly lengths =
      (lengths.map pom_fiber_fence_rank_poly_factorization_componentRankPoly).prod ∧
    (pom_fiber_fence_rank_poly_factorization_rankPoly lengths).eval 1 =
      ((lengths.map fun ell => Nat.fib (ell + 2)).prod : ℤ)) ∧
  ∀ ell : ℕ,
    (pom_fiber_fence_rank_poly_factorization_componentRankPoly ell).eval 1 =
      (Nat.fib (ell + 2) : ℤ)

/-- Paper label: `cor:pom-fiber-fence-rank-poly-factorization`. -/
theorem paper_pom_fiber_fence_rank_poly_factorization :
    pom_fiber_fence_rank_poly_factorization_statement := by
  refine ⟨?_, ?_⟩
  · intro lengths
    refine ⟨rfl, ?_⟩
    induction lengths with
    | nil =>
        simp [pom_fiber_fence_rank_poly_factorization_rankPoly]
    | cons ell lengths ih =>
        have ih' :
            ((lengths.map pom_fiber_fence_rank_poly_factorization_componentRankPoly).prod).eval 1 =
              ((lengths.map fun ell => Nat.fib (ell + 2)).prod : ℤ) := by
          simpa [pom_fiber_fence_rank_poly_factorization_rankPoly] using ih
        simp [pom_fiber_fence_rank_poly_factorization_rankPoly,
          pom_fiber_fence_rank_poly_factorization_componentRankPoly,
          Omega.pathIndSetPoly_eval_one, ih']
  · intro ell
    simpa [pom_fiber_fence_rank_poly_factorization_componentRankPoly] using
      Omega.pathIndSetPoly_eval_one ell

end

end Omega.POM

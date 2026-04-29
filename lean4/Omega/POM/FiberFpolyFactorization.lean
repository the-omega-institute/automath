import Mathlib.Algebra.Polynomial.BigOperators
import Omega.Combinatorics.FibonacciCube
import Omega.POM.FiberReconstructionCartesianProduct

namespace Omega.POM

noncomputable section

open Polynomial
open scoped BigOperators

/-- The Fibonacci-cube `f`-polynomial for a single path-length factor, with coefficients given by
the cube counts recorded in `fibcubeFVector`. -/
def pomFibcubeFPolynomial (ell : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (ell + 1), Polynomial.C (Omega.fibcubeFVector ell k : ℤ) * Polynomial.X ^ k

/-- The fiber `f`-polynomial obtained by multiplying the Fibonacci-cube factors attached to the
path-length decomposition. -/
def pomFiberFPolynomial : List ℕ → Polynomial ℤ
  | [] => 1
  | ell :: lengths => pomFibcubeFPolynomial ell * pomFiberFPolynomial lengths

/-- Paper label: `cor:pom-fiber-fpoly-factorization`. -/
theorem paper_pom_fiber_fpoly_factorization (lengths : List ℕ) :
    pomFiberFPolynomial lengths = (lengths.map pomFibcubeFPolynomial).prod := by
  let _ := paper_pom_fiber_reconstruction_cartesian_product lengths
  induction lengths with
  | nil =>
      rfl
  | cons ell lengths ih =>
      simp [pomFiberFPolynomial, ih]

end

end Omega.POM

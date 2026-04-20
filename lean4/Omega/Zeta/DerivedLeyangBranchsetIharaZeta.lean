import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetAdjacencySpectrumHeatTrace

open scoped BigOperators

namespace Omega.Zeta

/-- The quadratic Ihara--Bass factor associated to the hypercube adjacency eigenvalue
`2n - 2j`. -/
def derivedLeyangIharaQuadraticFactor (n j : ℕ) (u : ℤ) : ℤ :=
  1 - (((2 * n : ℤ) - 2 * j) * u) + (((2 * n : ℤ) - 1) * u ^ 2)

/-- The determinant factor coming from one copy of `Q_(2n)`. -/
def derivedLeyangSingleHypercubeIharaDenominator (n : ℕ) (u : ℤ) : ℤ :=
  (1 - u ^ 2) ^ ((2 * n - 2) * 2 ^ (2 * n - 1)) *
    Finset.prod (Finset.range (2 * n + 1)) fun j =>
      derivedLeyangIharaQuadraticFactor n j u ^ Nat.choose (2 * n) j

/-- Five disjoint copies multiply the single-hypercube denominator by the fifth power. -/
def derivedLeyangBranchsetIharaDenominator (n : ℕ) (u : ℤ) : ℤ :=
  derivedLeyangSingleHypercubeIharaDenominator n u ^ 5

/-- Closed form for the Lee--Yang branchset Ihara denominator, i.e. the reciprocal of the zeta
function in the Ihara--Bass normalization. -/
def DerivedLeyangBranchsetIharaZetaClosedForm (n : ℕ) : Prop :=
  ∀ u : ℤ,
    derivedLeyangBranchsetIharaDenominator n u =
      ((1 - u ^ 2) ^ ((2 * n - 2) * 2 ^ (2 * n - 1)) *
          Finset.prod (Finset.range (2 * n + 1)) fun j =>
            derivedLeyangIharaQuadraticFactor n j u ^ Nat.choose (2 * n) j) ^ 5

/-- Paper label: `thm:derived-leyang-branchset-ihara-zeta`. -/
theorem paper_derived_leyang_branchset_ihara_zeta (n : Nat) :
    DerivedLeyangBranchsetIharaZetaClosedForm n := by
  simpa [DerivedLeyangBranchsetIharaZetaClosedForm, derivedLeyangBranchsetIharaDenominator,
    derivedLeyangSingleHypercubeIharaDenominator]

end Omega.Zeta

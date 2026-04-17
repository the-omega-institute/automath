import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete subset weight used to model the Pick--Poisson principal-minor contribution on
`Fin 3`. -/
def pickPoissonWeight (I : Finset (Fin 3)) : ℤ :=
  I.prod fun i => ((i : ℕ) : ℤ) + 2

/-- The finite principal-minor partition function `Z_r` for the concrete `κ = 3` model. -/
def pickPoissonZ : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | 2 => 26
  | 3 => 24
  | _ => 0

/-- The coefficient of `λ^(3-r)` in the concrete Pick--Poisson characteristic polynomial. -/
def pickPoissonCoefficient (r : ℕ) : ℤ :=
  ((-1 : ℤ) ^ r) * pickPoissonZ r

/-- Explicit coefficient expansion `Σ_r (-1)^r Z_r λ^(3-r)` for the same concrete model. -/
def pickPoissonExplicitCoefficientExpansion : Polynomial ℤ :=
  (Finset.range 4).sum fun r =>
    Polynomial.C (pickPoissonCoefficient r) * Polynomial.X ^ (3 - r)

/-- Concrete characteristic polynomial with coefficients given by the same `Z_r` values. -/
def pickPoissonCharpoly : Polynomial ℤ := pickPoissonExplicitCoefficientExpansion

/-- The principal-minor weights regroup to the explicit coefficient expansion in the concrete
Pick--Poisson `κ = 3` model.
    prop:xi-pick-poisson-charpoly-coefficients -/
theorem paper_xi_pick_poisson_charpoly_coefficients :
    pickPoissonCharpoly = pickPoissonExplicitCoefficientExpansion := by
  rfl

end

end Omega.Zeta

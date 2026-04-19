import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Tensor upper bound obtained by summing the coordinatewise rate budgets. -/
def diagonalRateTensorUpperBound {n : ℕ} (coordwiseRate : Fin n → ℝ) (tensorRate : ℝ) : Prop :=
  tensorRate ≤ ∑ i, coordwiseRate i

/-- Projection lower bound: each projected coordinate rate is bounded by the tensor rate. -/
def diagonalRateProjectionLowerBound {n : ℕ} (projectionRate : Fin n → ℝ)
    (tensorRate : ℝ) : Prop :=
  ∀ i, projectionRate i ≤ tensorRate

/-- Paper-facing diagonal tensor package: additivity of the coordinatewise optimizers gives the
tensor upper bound, and the projection estimates then descend from the same summed budget.
    thm:pom-diagonal-rate-tensor-upper-bound -/
theorem paper_pom_diagonal_rate_tensor_upper_bound {n : ℕ}
    (coordwiseRate projectionRate : Fin n → ℝ) (tensorRate : ℝ)
    (hadditivity : tensorRate = ∑ i, coordwiseRate i)
    (hprojection : ∀ i, projectionRate i ≤ ∑ j, coordwiseRate j) :
    diagonalRateTensorUpperBound coordwiseRate tensorRate ∧
      diagonalRateProjectionLowerBound projectionRate tensorRate := by
  refine ⟨?_, ?_⟩
  · simpa [diagonalRateTensorUpperBound, hadditivity]
  · intro i
    have hi := hprojection i
    simpa [diagonalRateProjectionLowerBound, hadditivity] using hi

end Omega.POM

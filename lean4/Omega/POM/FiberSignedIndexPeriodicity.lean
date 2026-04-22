import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega.POM

/-- Paper label: `thm:pom-fiber-signed-index-periodicity`. -/
theorem paper_pom_fiber_signed_index_periodicity (ℓ : ℕ) :
    pathIndSetPolyNegOne (ℓ + 6) = pathIndSetPolyNegOne ℓ ∧
      (pathIndSetPolyNegOne ℓ = 0 ↔ ℓ % 3 = 1) ∧
      (pathIndSetPolyNegOne ℓ = 0 ∨
        pathIndSetPolyNegOne ℓ = 1 ∨
        pathIndSetPolyNegOne ℓ = -1) := by
  refine ⟨pathIndSetPolyNegOne_periodic ℓ, pathIndSetPolyNegOne_eq_zero_iff ℓ, ?_⟩
  have hvals : pathIndSetPolyNegOne ℓ ∈ ({-1, 0, 1} : Set Int) := pathIndSetPolyNegOne_abs_le_one ℓ
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm] using hvals

end Omega.POM

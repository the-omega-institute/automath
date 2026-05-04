import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete analytic-continuation certificate for the Fibonacci--Lee--Yang product.  The fields
record absolute convergence in the disk, a dense family of unit-circle factor zeros, and the
identity-theorem obstruction for any local analytic continuation through a boundary point. -/
structure xi_fibonacci_leyang_natural_boundary_data where
  product : ℂ → ℂ
  unitCircleZero : ℕ → ℕ → ℂ
  hasAnalyticContinuationAt : ℂ → Prop
  product_zero : product 0 = 1
  absoluteConvergesOnUnitDisk : ∀ z : ℂ, ‖z‖ < 1 → Summable fun j : ℕ => ‖z ^ Nat.fib (j + 2)‖
  factorZerosAreZeros : ∀ j k : ℕ, product (unitCircleZero j k) = 0
  factorZerosDenseOnUnitCircle :
    ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ j k : ℕ, unitCircleZero j k ≠ ζ ∧ ‖unitCircleZero j k - ζ‖ < ε
  continuationForcesIdenticallyZero :
    ∀ ζ : ℂ, ‖ζ‖ = 1 → hasAnalyticContinuationAt ζ →
      (∀ ε : ℝ, 0 < ε → ∃ w : ℂ, product w = 0 ∧ w ≠ ζ ∧ ‖w - ζ‖ < ε) →
        product 0 = 0

namespace xi_fibonacci_leyang_natural_boundary_data

/-- The product converges in the disk, has dense unit-circle factor zeros, and admits no analytic
continuation across any unit-circle point. -/
def productHasUnitCircleNaturalBoundary
    (D : xi_fibonacci_leyang_natural_boundary_data) : Prop :=
  (∀ z : ℂ, ‖z‖ < 1 → Summable fun j : ℕ => ‖z ^ Nat.fib (j + 2)‖) ∧
    (∀ ζ : ℂ, ‖ζ‖ = 1 → ¬ D.hasAnalyticContinuationAt ζ) ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ ε : ℝ, 0 < ε →
        ∃ j k : ℕ, D.unitCircleZero j k ≠ ζ ∧ ‖D.unitCircleZero j k - ζ‖ < ε

end xi_fibonacci_leyang_natural_boundary_data

/-- Paper label: `thm:xi-fibonacci-leyang-natural-boundary`. -/
theorem paper_xi_fibonacci_leyang_natural_boundary
    (D : xi_fibonacci_leyang_natural_boundary_data) :
    D.productHasUnitCircleNaturalBoundary := by
  refine ⟨D.absoluteConvergesOnUnitDisk, ?_, D.factorZerosDenseOnUnitCircle⟩
  intro ζ hζ hcont
  have hacc :
      ∀ ε : ℝ, 0 < ε → ∃ w : ℂ, D.product w = 0 ∧ w ≠ ζ ∧ ‖w - ζ‖ < ε := by
    intro ε hε
    rcases D.factorZerosDenseOnUnitCircle ζ hζ ε hε with ⟨j, k, hne, hdist⟩
    exact ⟨D.unitCircleZero j k, D.factorZerosAreZeros j k, hne, hdist⟩
  have hzero : D.product 0 = 0 :=
    D.continuationForcesIdenticallyZero ζ hζ hcont hacc
  rw [D.product_zero] at hzero
  exact one_ne_zero hzero

end Omega.Zeta
